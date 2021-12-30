module Data.BinaryTree.Functions where

open import Data.BinaryTree
import      Lvl
open import Type

private variable ℓ ℓᵢ ℓₗ ℓₙ ℓₒ : Lvl.Level
private variable N N₁ N₂ L T A B C : Type{ℓ}

foldTree : (L → T) → (N → T → T → T) → (BinaryTree L N → T)
foldTree l n = elim(_) l n

open import Data using (Unit ; <>)
open import Data.Boolean as Boolean using (Bool ; 𝑇 ; 𝐹)
open import Data.Option as Option using (Option ; Some ; None)
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional as Fn using (const ; _$_ ; _∘_ ; _∘₂_ ; _on₂_)
open import Numeral.Natural
open import Numeral.Natural.Function
open import Numeral.Natural.Oper hiding (_^_)
open import Syntax.Function

-- Constructs an empty tree.
emptyTree : BinaryTree{ℓₗ} Unit N
emptyTree = Leaf <>

-- Constructs a tree with a single node.
singletonTree : N → BinaryTree{ℓₗ} Unit N
singletonTree a = Node a emptyTree emptyTree

-- Decides whether a tree is a leaf.
isLeaf : BinaryTree L N → Bool
isLeaf (Leaf _)     = 𝑇
isLeaf (Node _ _ _) = 𝐹

-- Decides whether a tree is a node.
isNode : BinaryTree L N → Bool
isNode (Leaf _)     = 𝐹
isNode (Node _ _ _) = 𝑇

-- The root node of the tree, if there is any.
root : BinaryTree L N → Option(N)
root (Leaf _)     = None
root (Node a _ _) = Some a

-- Flips the tree, swapping the left and right branches of all nodes.
-- Alternative implementation:
--   flip (Leaf l)     = Leaf l
--   flip (Node n l r) = Node n (flip r) (flip l)
-- Example:
--   flip(Node 0 (Node 10 (Leaf 20) (Leaf 21)) (Node 11 (Leaf 22) (Node 23 (Leaf 30) (Leaf 31)))) = Node 0 (Node 11 (Node 23 (Leaf 31) (Leaf 30)) (Leaf 22)) (Node 10 (Leaf 21) (Leaf 20))
--         ╭────  0 ────╮                          ╭────  0 ────╮
--    ╭── 10 ──╮    ╭── 11 ──╮     (flip)     ╭── 11 ──╮    ╭── 10 ──╮
--   20        21  22      ╭ 23 ╮    ↦     ╭ 23 ╮      22  21        20
--                        30    31        31    30
flip : BinaryTree L N → BinaryTree L N
flip = foldTree Leaf (Fn.swap ∘ Node)

-- Example:
--               ╭────────────────────────  0 ────────────────────────╮
--    ╭──────── 10 ────────╮                                ╭──────── 11 ────────╮
--   20              ╭──── 21 ────╮                  ╭──── 22 ────╮        ╭──── 23 ────╮
--                  30        ╭── 31 ──╮            32          ╭ 33 ╮    34            35
--                         ╭ 40 ╮      41                      42    43
--                        50    51
-- open import Data.List
-- test = {!foldPostOrderDepthFirst(_⊰_)(_⊰_) ∅ $ Node 0 (Node 10 (Leaf 20) (Node 21 (Leaf 30) (Node 31 (Node 40 (Leaf 50) (Leaf 51)) (Leaf 41)))) (Node 11 (Node 22 (Leaf 32) (Node 33 (Leaf 42) (Leaf 43))) (Node 23 (Leaf 34) (Leaf 35)))!}

-- Example (Traversal order):
--               ╭────────────────────────  0 ────────────────────────╮
--    ╭────────  1 ────────╮                                ╭──────── 10 ────────╮
--    2              ╭──── 3  ────╮                  ╭──── 11 ────╮        ╭──── 16 ────╮
--                   4        ╭── 5  ──╮            12          ╭ 13 ╮    17            18
--                         ╭  6 ╮      9                       14    15
--                         7    8
-- Alternative implementation:
--   foldPreOrderDepthFirst(f)(_▫_) id (Leaf a)     = f a
--   foldPreOrderDepthFirst(f)(_▫_) id (Node a l r) =
--     a ▫_                                      $
--     Fn.swap(foldPreOrderDepthFirst(f)(_▫_)) l $
--     Fn.swap(foldPreOrderDepthFirst(f)(_▫_)) r $
--     id
foldPreOrderDepthFirst : (L → T → T) → (N → T → T) → T → BinaryTree L N → T
foldPreOrderDepthFirst(_▫ₗ_)(_▫ₙ_) = Fn.swap $ foldTree(_▫ₗ_) (\a l r → (a ▫ₙ_) ∘ l ∘ r)

-- Example (Traversal order):
--               ╭────────────────────────  9 ────────────────────────╮
--    ╭────────  1 ────────╮                                ╭──────── 15 ────────╮
--    0              ╭──── 3  ────╮                  ╭──── 11 ────╮        ╭──── 17 ────╮
--                   2        ╭── 7  ──╮            10          ╭ 13 ╮    16            18
--                         ╭  5 ╮      8                       12    14
--                         4    6 
-- Alternative implementation:
--   foldInOrderDepthFirst(f)(_▫_) id (Leaf a)     = f a
--   foldInOrderDepthFirst(f)(_▫_) id (Node a l r) =
--     Fn.swap(foldInOrderDepthFirst(f)(_▫_)) l $
--     a ▫_                                     $
--     Fn.swap(foldInOrderDepthFirst(f)(_▫_)) r $
--     id
foldInOrderDepthFirst : (L → T → T) → (N → T → T) → T → BinaryTree L N → T
foldInOrderDepthFirst(_▫ₗ_)(_▫ₙ_) = Fn.swap $ foldTree(_▫ₗ_) (\a l r → l ∘ (a ▫ₙ_) ∘ r)

-- Example (Traversal order):
--               ╭──────────────────────── 18 ────────────────────────╮
--    ╭────────  8 ────────╮                                ╭──────── 17 ────────╮
--    0              ╭──── 7  ────╮                  ╭──── 13 ────╮        ╭──── 16 ────╮
--                   1        ╭── 6  ──╮             9          ╭ 12 ╮    14            15
--                         ╭  4 ╮      5                       10    11
--                         2    3 
-- Alternative implementation:
--   foldPostOrderDepthFirst(f)(_▫_) id (Leaf a)     = f a
--   foldPostOrderDepthFirst(f)(_▫_) id (Node a l r) =
--     Fn.swap(foldPostOrderDepthFirst(f)(_▫_)) l $
--     Fn.swap(foldPostOrderDepthFirst(f)(_▫_)) r $
--     a ▫_                                       $
--     id
foldPostOrderDepthFirst : (L → T → T) → (N → T → T) → T → BinaryTree L N → T
foldPostOrderDepthFirst(_▫ₗ_)(_▫ₙ_) = Fn.swap $ foldTree(_▫ₗ_) (\a l r → l ∘ r ∘ (a ▫ₙ_))

-- Alternative implementation:
--   foldReversedPreOrderDepthFirst(f)(_▫_) id (Leaf a)     = f a
--   foldReversedPreOrderDepthFirst(f)(_▫_) id (Node a l r) =
--     a ▫_                                              $
--     Fn.swap(foldReversedPreOrderDepthFirst(f)(_▫_)) r $
--     Fn.swap(foldReversedPreOrderDepthFirst(f)(_▫_)) l $
--     id
foldReversedPreOrderDepthFirst : (L → T → T) → (N → T → T) → T → BinaryTree L N → T
foldReversedPreOrderDepthFirst(_▫ₗ_)(_▫ₙ_) = Fn.swap $ foldTree(_▫ₗ_) (\a l r → (a ▫ₙ_) ∘ r ∘ l)

-- Alternative implementation:
--   foldReversedInOrderDepthFirst(f)(_▫_) id (Leaf a)     = f a
--   foldReversedInOrderDepthFirst(f)(_▫_) id (Node a l r) =
--     Fn.swap(foldReversedInOrderDepthFirst(f)(_▫_)) r $
--     a ▫_                                             $
--     Fn.swap(foldReversedInOrderDepthFirst(f)(_▫_)) l $
--     id
foldReversedInOrderDepthFirst : (L → T → T) → (N → T → T) → T → BinaryTree L N → T
foldReversedInOrderDepthFirst(_▫ₗ_)(_▫ₙ_) = Fn.swap $ foldTree(_▫ₗ_) (\a l r → r ∘ (a ▫ₙ_) ∘ l)

-- Alternative implementation:
--   foldReversedPostOrderDepthFirst(f)(_▫_) id (Leaf a)     = f a
--   foldReversedPostOrderDepthFirst(f)(_▫_) id (Node a l r) =
--     Fn.swap(foldReversedPostOrderDepthFirst(f)(_▫_)) r $
--     Fn.swap(foldReversedPostOrderDepthFirst(f)(_▫_)) l $
--     a ▫_                                               $
--     id
foldReversedPostOrderDepthFirst : (L → T → T) → (N → T → T) → T → BinaryTree L N → T
foldReversedPostOrderDepthFirst(_▫ₗ_)(_▫ₙ_) = Fn.swap $ foldTree(_▫ₗ_) (\a l r → r ∘ l ∘ (a ▫ₙ_))

-- The size is the number of nodes in the tree.
-- Alternative implementation:
--   size (Leaf _)     = 𝟎
--   size (Node _ l r) = 𝐒(size(l) + size(r))
size : BinaryTree L N → ℕ
size = foldTree(const 𝟎) (const(𝐒 ∘₂ (_+_)))

-- The number of leaves in the tree.
-- Alternative implementation:
--   numberOfLeaves (Leaf _)     = 1
--   numberOfLeaves (Node _ l r) = numberOfLeaves(l) + numberOfLeaves(r)
numberOfLeaves : BinaryTree L N → ℕ
numberOfLeaves = foldTree(const 1) (const(_+_))

-- The height is the length of the longest node-path from the root.
-- Alternative implementation:
--   height (Leaf _)     = 𝟎
--   height (Node _ l r) = 𝐒(max(height l) (height r))
height : BinaryTree L N → ℕ
height = foldTree(const 𝟎) (const(𝐒 ∘₂ max))

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

rotateₗ : BinaryTree L N → Option(BinaryTree L N)
rotateₗ (Leaf a)                  = None
rotateₗ (Node a l (Leaf b))       = None
rotateₗ (Node a l (Node b rl rr)) = Some(Node b (Node a l rl) rr)

rotateᵣ : BinaryTree L N → Option(BinaryTree L N)
rotateᵣ(Leaf a)                  = None
rotateᵣ(Node a (Leaf b) r)       = None
rotateᵣ(Node a (Node b ll lr) r) = Some(Node b ll (Node a lr r))

import Data.Option.Functions as Option

rotateₗ₀ : BinaryTree L N → BinaryTree L N
rotateₗ₀ t = (rotateₗ t) Option.or t

rotateᵣ₀ : BinaryTree L N → BinaryTree L N
rotateᵣ₀ t = (rotateᵣ t) Option.or t

-- The difference in height between the shallowest and the deppest leaf in the tree.
-- Or in other words, the difference in length between the shortest and the longest path to a leaf.
heightDifference : BinaryTree L N → ℕ
heightDifference = Tuple.uncurry(_𝄩_) ∘ (foldTree(const(𝟎 , 𝟎)) (const(Tuple.map₂ (𝐒 ∘₂ min) (𝐒 ∘₂ max))))

-- If a tree is perfect and of a certain height.
-- In other words, whether the length to any of the leaves are all the same and is the specified number.
isHeightPerfect : ℕ → BinaryTree L N → Bool
isHeightPerfect 𝟎                  = isLeaf
isHeightPerfect (𝐒 _) (Leaf _)     = 𝐹
isHeightPerfect (𝐒 n) (Node _ l r) = (isHeightPerfect n l) && (isHeightPerfect n r)

open import Data.Boolean
open import Numeral.Natural.Oper.Comparisons

-- When a tree is perfect, the perfect height is the length to any of the leaves in this tree.
-- This also decides whether a tree is perfect or not.
-- Alternative implementation:
--   perfectHeight (Leaf _)     = Some 𝟎
--   perfectHeight (Node _ l r) = (perfectHeight l) Option.andThen (nₗ ↦ ((perfectHeight r) Option.andThen (nᵣ ↦ if(nₗ ≡? nᵣ) then Some(𝐒(nₗ)) else None)))
perfectHeight : BinaryTree L N → Option(ℕ)
perfectHeight = foldTree (const(Some 𝟎)) (const(l ↦ r ↦ (l Option.andThen(nₗ ↦ r Option.andThen(nᵣ ↦ if(nₗ ≡? nᵣ) then Some(𝐒(nₗ)) else None)))))
