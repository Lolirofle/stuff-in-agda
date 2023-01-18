module Data.DependentWidthTree where

import      Lvl
open import Functional using (id)
open import DependentFunctional
open import Numeral.Finite
open import Numeral.Natural
open import Type

private variable ℓ ℓᵢ ℓₗ ℓₙ ℓₒ : Lvl.Level
private variable N N₁ N₂ L T A B : Type{ℓ}

module _ {N : Type{ℓₙ}} (Index : N → Type{ℓᵢ}) where
  -- A tree where the number of children depends on the data stored in a node.
  -- Leaves should be represented by having nodes that indicate no children.
  -- Note: A tree that have no leaves will not be constructible.
  data Tree : Type{ℓₙ Lvl.⊔ ℓᵢ} where
    Node : (node : N) → (Index(node) → Tree) → Tree

  -- The data of the root node of a tree.
  root : Tree → N
  root (Node node _) = node

  -- The children of a node of a tree.
  -- They are indexed by `Index`.
  child : (t : Tree) → (Index(root t) → Tree)
  child (Node _ child) = child

  Tree-elim : ∀{P : Tree → Type{ℓ}} → (∀(node)(child) → (∀(i) → P(child(i))) → P(Node node child)) → ((tree : Tree) → P(tree))
  Tree-elim{P = P} f (Node node child) = f node child (Tree-elim{P = P} f ∘ child)

  open import Logic.Propositional
  -- It is impossible for every node to have at least one child while at the same time a tree exists.
  -- Note that constructively, this is not enough to prove the existence of leaves.
  Tree-no-leaves-impossibility : (∀{node} → Index(node)) → Tree → ⊥
  Tree-no-leaves-impossibility p (Node n c) = Tree-no-leaves-impossibility p (c(p{n}))

module _ {N : Type{ℓₙ}} (width : N → ℕ) where
  FiniteTree = Tree(𝕟 ∘ width)

module _ where
  open import Data.Boolean

  -- A tree of finite variating width holding no data other than the structure of the tree (the number of children for each node).
  -- Example:
  --   3:
  --   ├1:
  --   │└0
  --   ├2:
  --   │├0
  --   │└1:
  --   │ └0
  --   └0
  FiniteTreeStructure = FiniteTree id

  -- An empty tree contains no children.
  -- This is also functioning as a leaf to a tree.
  empty : FiniteTreeStructure
  empty = Node 0 \()

  -- A tree containing a single child that contains a leaf.
  singleton : FiniteTreeStructure
  singleton = Node 1 \{𝟎 → empty}

  isLeaf : FiniteTreeStructure → Bool
  isLeaf(Node 𝟎     _) = 𝑇
  isLeaf(Node (𝐒 _) _) = 𝐹

  isNode : FiniteTreeStructure → Bool
  isNode(Node 𝟎     _) = 𝐹
  isNode(Node (𝐒 _) _) = 𝑇

  import      Numeral.CoordinateVector as CoordinateVector
  open import Numeral.Natural.Function
  open import Numeral.Natural.Oper

  -- The height is the length of the longest path from the root node.
  -- Alternative implementation (will not pass the termination checker):
  --   height(Node 𝟎         child) = 𝟎
  --   height(Node (𝐒(node)) child) = 𝐒(CoordinateVector.foldᵣ(max ∘ height) 𝟎 child)
  height : FiniteTreeStructure → ℕ
  height = Tree-elim 𝕟 (\{𝟎 _ _ → 𝟎 ; (𝐒(c)) _ prev → 𝐒(CoordinateVector.foldᵣ max 𝟎 prev)})

  -- The size of a tree is the number of nodes in the tree.
  size : FiniteTreeStructure → ℕ
  size = Tree-elim 𝕟 (\{𝟎 _ _ → 𝟎 ; (𝐒(c)) _ prev → 𝐒(CoordinateVector.foldᵣ (_+_) 𝟎 prev)})
