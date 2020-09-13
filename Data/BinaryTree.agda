module Data.BinaryTree where

import      Lvl
open import Type

private variable ℓ ℓᵢ ℓₗ ℓₙ ℓₒ : Lvl.Level
private variable N N₁ N₂ L T A B : Type{ℓ}

data BinaryTree (L : Type{ℓₗ}) (N : Type{ℓₙ}) : Type{ℓₗ Lvl.⊔ ℓₙ} where
  Leaf : L → BinaryTree L N
  Node : N → BinaryTree L N → BinaryTree L N → BinaryTree L N

open import Data using (Unit ; <>)
open import Data.Boolean
open import Data.Option
open import Data.Tuple using (_⨯_ ; _,_)
open import Functional as Fn using (_$_)
open import Numeral.Natural
open import Numeral.Natural.Function
open import Numeral.Natural.Oper hiding (_^_)

emptyTree : BinaryTree{ℓₗ} Unit N
emptyTree = Leaf <>

singleton : N → BinaryTree{ℓₗ} Unit N
singleton a = Node a emptyTree emptyTree

isLeaf : BinaryTree L N → Bool
isLeaf (Leaf _)     = 𝑇
isLeaf (Node _ _ _) = 𝐹

isNode : BinaryTree L N → Bool
isNode (Leaf _)     = 𝐹
isNode (Node _ _ _) = 𝑇

root : BinaryTree L N → Option(N)
root (Leaf _)     = None
root (Node a _ _) = Some a

flip : BinaryTree L N → BinaryTree L N
flip (Leaf l)     = Leaf l
flip (Node n l r) = Node n (flip r) (flip l)

foldPreOrderDepthFirst : (L → T → T) → (N → T → T) → T → BinaryTree L N → T
foldPreOrderDepthFirst(_▫ₗ_)(_▫ₙ_) id (Leaf a)     = a ▫ₗ id
foldPreOrderDepthFirst(_▫ₗ_)(_▫ₙ_) id (Node a l r) =
  a ▫ₙ_                                         $
  Fn.swap(foldPreOrderDepthFirst(_▫ₗ_)(_▫ₙ_)) l $
  Fn.swap(foldPreOrderDepthFirst(_▫ₗ_)(_▫ₙ_)) r $
  id

foldInOrderDepthFirst : (L → T → T) → (N → T → T) → T → BinaryTree L N → T
foldInOrderDepthFirst(_▫ₗ_)(_▫ₙ_) id (Leaf a)     = a ▫ₗ id
foldInOrderDepthFirst(_▫ₗ_)(_▫ₙ_) id (Node a l r) =
  Fn.swap(foldInOrderDepthFirst(_▫ₗ_)(_▫ₙ_)) l $
  a ▫ₙ_                                        $
  Fn.swap(foldInOrderDepthFirst(_▫ₗ_)(_▫ₙ_)) r $
  id

foldPostOrderDepthFirst : (L → T → T) → (N → T → T) → T → BinaryTree L N → T
foldPostOrderDepthFirst(_▫ₗ_)(_▫ₙ_) id (Leaf a)     = a ▫ₗ id
foldPostOrderDepthFirst(_▫ₗ_)(_▫ₙ_) id (Node a l r) =
  Fn.swap(foldPostOrderDepthFirst(_▫ₗ_)(_▫ₙ_)) l $
  Fn.swap(foldPostOrderDepthFirst(_▫ₗ_)(_▫ₙ_)) r $
  a ▫ₙ_                                          $
  id

foldReversedPreOrderDepthFirst : (L → T → T) → (N → T → T) → T → BinaryTree L N → T
foldReversedPreOrderDepthFirst(_▫ₗ_)(_▫ₙ_) id (Leaf a)     = a ▫ₗ id
foldReversedPreOrderDepthFirst(_▫ₗ_)(_▫ₙ_) id (Node a l r) =
  a ▫ₙ_                                                 $
  Fn.swap(foldReversedPreOrderDepthFirst(_▫ₗ_)(_▫ₙ_)) r $
  Fn.swap(foldReversedPreOrderDepthFirst(_▫ₗ_)(_▫ₙ_)) l $
  id

foldReversedInOrderDepthFirst : (L → T → T) → (N → T → T) → T → BinaryTree L N → T
foldReversedInOrderDepthFirst(_▫ₗ_)(_▫ₙ_) id (Leaf a)     = a ▫ₗ id
foldReversedInOrderDepthFirst(_▫ₗ_)(_▫ₙ_) id (Node a l r) =
  Fn.swap(foldReversedInOrderDepthFirst(_▫ₗ_)(_▫ₙ_)) r $
  a ▫ₙ_                                                $
  Fn.swap(foldReversedInOrderDepthFirst(_▫ₗ_)(_▫ₙ_)) l $
  id

foldReversedPostOrderDepthFirst : (L → T → T) → (N → T → T) → T → BinaryTree L N → T
foldReversedPostOrderDepthFirst(_▫ₗ_)(_▫ₙ_) id (Leaf a)     = a ▫ₗ id
foldReversedPostOrderDepthFirst(_▫ₗ_)(_▫ₙ_) id (Node a l r) =
  Fn.swap(foldReversedPostOrderDepthFirst(_▫ₗ_)(_▫ₙ_)) r $
  Fn.swap(foldReversedPostOrderDepthFirst(_▫ₗ_)(_▫ₙ_)) l $
  a ▫ₙ_                                                  $
  id

-- The size is the number of nodes in the tree.
size : BinaryTree L N → ℕ
size (Leaf _)     = 𝟎
size (Node _ l r) = 𝐒(size(l) + size(r))

-- The number of leaves in the tree.
numberOfLeaves : BinaryTree L N → ℕ
numberOfLeaves (Leaf _)     = 1
numberOfLeaves (Node _ l r) = numberOfLeaves(l) + numberOfLeaves(r)

-- The height is the length of the longest path from the root.
height : BinaryTree L N → ℕ
height (Leaf _)     = 𝟎
height (Node _ l r) = 𝐒(max (height l) (height r))

open import Data.Boolean.Operators
open        Data.Boolean.Operators.Programming

isFull : BinaryTree L N → Bool
isFull (Leaf _)                               = 𝑇
isFull (Node _ (Leaf _)        (Leaf _))      = 𝑇
isFull (Node _ (Node _ _ _)    (Leaf _))      = 𝐹
isFull (Node _ (Leaf _)        (Node _ _ _))  = 𝐹
isFull (Node _ l@(Node _ _ _) r@(Node _ _ _)) = isFull l && isFull r

open import Data.List
import      Data.List.Functions as List

treesOfDepth : ℕ → BinaryTree L N → List(BinaryTree L N)
treesOfDepth 𝟎      tree         = tree ⊰ ∅
treesOfDepth (𝐒(_)) (Leaf _)     = ∅
treesOfDepth (𝐒(n)) (Node _ l r) = (treesOfDepth n l) List.++ (treesOfDepth n r)
