module Data.FixedTree where

import      Lvl
open import Data hiding (empty)
open import Data.List
open import Data.Tuple using (_⨯_ ; _,_)
open import Data.Tuple.Raise
open import Functional as Fn
open import Numeral.Natural
open import Type

private variable ℓ ℓᵢ ℓₗ ℓₙ ℓₒ : Lvl.Level
private variable n : ℕ
private variable N N₁ N₂ L T A B : Type{ℓ}

module _ {I : Type{ℓᵢ}} (children : I → ℕ) (step : I → I) (L : Type{ℓₗ}) (N : Type{ℓₙ}) where
  data Tree₊ : I → Type{ℓₗ Lvl.⊔ ℓₙ Lvl.⊔ ℓᵢ} where
    Leaf : ∀{i} → L → Tree₊(i)
    Node : ∀{i} → N → (Tree₊(step i) ^ children(step i)) → Tree₊(i)

  data Tree₋ : I → Type{ℓₗ Lvl.⊔ ℓₙ Lvl.⊔ ℓᵢ} where
    Leaf : ∀{i} → L → Tree₋(i)
    Node : ∀{i} → N → (Tree₋(i) ^ children(i)) → Tree₋(step i)

-- Alternative definition:
--   data FixedTree (n : ℕ) (L : Type{ℓₗ}) (N : Type{ℓₙ}) : Type{ℓₗ Lvl.⊔ ℓₙ} where
--     Leaf : L → FixedTree(n) L N
--     Node : N → ((FixedTree(n) L N) ^ n) → FixedTree(n) L N
FixedTree : ℕ → Type{ℓₗ} → Type{ℓₙ} → Type{ℓₗ Lvl.⊔ ℓₙ}
FixedTree(n) L N = Tree₊ id id L N n

open import Data using (Unit ; <>)
open import Data.Boolean
open import Data.Boolean.Operators
open        Data.Boolean.Operators.Programming
open import Data.Option
import      Data.Tuple.Raiseᵣ.Functions as Raise
open import Logic.Propositional
open import Logic.Predicate
open import Numeral.Finite
open import Numeral.Finite.Oper.Comparisons
open import Numeral.Natural.Function
open import Numeral.Natural.Oper hiding (_^_)

emptyTree : FixedTree{ℓₗ}(n) Unit N
emptyTree{n = n} = Leaf <>

singleton : N → FixedTree{ℓₗ}(n) Unit N
singleton{n = n} a = Node a (Raise.repeat n emptyTree)

isLeaf : FixedTree(n) L N → Bool
isLeaf (Leaf _)   = 𝑇
isLeaf (Node _ _) = 𝐹

isNode : FixedTree(n) L N → Bool
isNode (Leaf _)   = 𝐹
isNode (Node _ _) = 𝑇

root : FixedTree(n) L N → Option(N)
root (Leaf _)   = None
root (Node a _) = Some a

foldChildNodesᵣ : (((FixedTree(n) L N) ^ n) → N → T → T) → T → FixedTree(n) L N → T
foldChildNodesᵣ        join id (Leaf _)   = id
foldChildNodesᵣ{n = n} join id (Node _ c) = Raise.foldᵣ{n} (\{(Leaf _) → Fn.id ; (Node a c) → join c a}) id c

-- TODO: Is it correct? Also termination checker
{-
testfoldᵣ : ∀{n : ℕ}{ℓ₁ ℓ₂}{A : Type{ℓ₁}}{B : Type{ℓ₂}} → (A → B → B) → B → (FixedTree(n)(A) ^ n) → B
testfoldᵣ {0}       (_▫_) id _              = id
testfoldᵣ {1}       (_▫_) id Leaf           = id
testfoldᵣ {1}       (_▫_) id (Node a c)     = a ▫ testfoldᵣ {1} (_▫_) id c
-- x ▫ def
testfoldᵣ {𝐒(𝐒(n))} (_▫_) def (x , xs) = {!!}
-- x ▫ testfoldᵣ {𝐒(n)} (_▫_) def xs

fold : (A → B → B) → B → FixedTree(n)(A) → B
fold        (_▫_) id Leaf       = id
fold{n = n} (_▫_) id (Node a c) = a ▫ Raise.foldᵣ{n} (\{Leaf -> Fn.id ; node@(Node _ _) acc → fold{n = n} (_▫_) acc node}) id c

fold : (A → B → B) → B → FixedTree(n)(A) → B
fold{A = A}{B = B}{n = n} (_▫_) id tree = foldChildNodesᵣ ({!swap(fold{n = n} (_▫_))!}) id tree where
  f : ∀{n₁ n₂} → FixedTree(n₁)(A) ^ n₂ → A → B → B
  f {n₂ = 0}        <>           a acc = a ▫ acc
  f {n₂ = 1}        Leaf         a acc = a ▫ acc
  f {n₂ = 1}        (Node ca cc) a acc = f cc a (ca ▫ acc)
  -- ca ▫ (a ▫ acc)
  f {n₂ = 𝐒(𝐒(n₂))} c a acc = {!!}

testfoldDepthFirst : (A → B → B) → B → FixedTree(n)(A) → B
testfoldᵣ : ∀{n₁ n₂ : ℕ}{ℓ₁ ℓ₂}{A : Type{ℓ₁}}{B : Type{ℓ₂}} → (A → B → B) → B → (FixedTree(n₁)(A) ^ n₂) → B

testfoldDepthFirst        (_▫_) id Leaf       = id
testfoldDepthFirst{n = n} (_▫_) id (Node a c) = a ▫ testfoldᵣ{n} (_▫_) id c

testfoldᵣ          {n₂ = 0}        (_▫_) def _        = def
testfoldᵣ {n₁ = n₁}{n₂ = 1}        (_▫_) def x        = testfoldDepthFirst{n = n₁} (_▫_) def x
-- testfoldᵣ {n₂ = 𝐒(𝐒(n₂))} (_▫_) def (x , xs) = swap(testfoldDepthFirst{n = _} (_▫_)) x (testfoldᵣ {n₂ = 𝐒(n₂)} (_▫_) def xs)

testfoldᵣ : ∀{n₁ n₂ : ℕ}{ℓ₁ ℓ₂}{A : Type{ℓ₁}}{B : Type{ℓ₂}} → (A → B → B) → B → (FixedTree(n₁)(A) ^ n₂) → B
testfoldᵣ {n₂ = 0}       (_▫_) id <>              = id
testfoldᵣ {n₂ = 1}       (_▫_) id Leaf            = id
testfoldᵣ {n₂ = 1}       (_▫_) id (Node a c)      = a ▫ testfoldᵣ(_▫_) id c
testfoldᵣ {n₂ = 𝐒(𝐒(n))} (_▫_) id (Leaf     , xs) = testfoldᵣ(_▫_) id xs
testfoldᵣ {n₂ = 𝐒(𝐒(n))} (_▫_) id (Node a c , xs) = testfoldᵣ(_▫_) (a ▫ testfoldᵣ(_▫_) id xs) c
-}

{-# TERMINATING #-}
foldDepthFirst : (N → T → T) → T → FixedTree(n) L N → T
foldDepthFirst        (_▫_) id (Leaf _)   = id
foldDepthFirst{n = n} (_▫_) id (Node a c) = a ▫ Raise.foldᵣ{n} (swap(foldDepthFirst{n = n} (_▫_))) id c

import      Data.Tuple.RaiseTypeᵣ.Functions as RaiseType
open import Function.Multi
import      Function.Multi.Functions as Multi

{-# TERMINATING #-}
FixedTree-induction : ∀{P : FixedTree{ℓₗ}{ℓₙ}(n) L N → Type{ℓ}} → (∀{l} → P(Leaf l)) → ((a : N) → (c : (FixedTree(n) L N) ^ n) → (RaiseType.from-[^] (Raise.map P(c)) ⇉ P(Node a c))) → ((tree : FixedTree(n) L N) → P(tree))
FixedTree-induction                       base _    (Leaf l)   = base{l}
FixedTree-induction {n = 0}               _    step (Node a c) = step a c
FixedTree-induction {n = 1}               base step (Node a c) = step a c (FixedTree-induction{n = 1} base step c)
FixedTree-induction {n = 𝐒(𝐒(n))} {P = P} base step (Node a c) = recurseChildren{𝐒(𝐒(n))}(step a c) where
  recurseChildren : ∀{L}{l : _ ^ L} → (RaiseType.from-[^] (Raise.map P(l)) ⇉ P(Node a c)) → P(Node a c)
  recurseChildren {0}                 = id
  recurseChildren {1}       {l}     p = p(FixedTree-induction{n = 𝐒(𝐒(n))} base step l)
  recurseChildren {𝐒(𝐒(L))} {x , l} p = recurseChildren{𝐒(L)}{l} (p(FixedTree-induction{n = 𝐒(𝐒(n))} base step x))

-- The size is the number of nodes in the tree.
-- Alternative implementation:
--   size{n = n}{L = L}{N = N} = FixedTree-induction 𝟎 (rec{w = n}) where
--     rec : ∀{w} → (a : N) → (c : (FixedTree(n) L N) ^ w) → RaiseType.from-[^] (Raise.map{w} (const ℕ)(c)) ⇉ ℕ
--     rec {w = 0}       _  _         = 1
--     rec {w = 1}       _  _       n = 𝐒(n)
--     rec {w = 𝐒(𝐒(w))} a  (_ , c) n = Multi.compose(𝐒(w)) (n +_) (rec{w = 𝐒(w)} a c)
{-# TERMINATING #-}
size : FixedTree(n) L N → ℕ
size (Leaf _)   = 𝟎
size (Node _ c) = 𝐒(Raise.foldᵣ((_+_) ∘ size) 𝟎 c)

-- The height is the length of the longest path from the root node.
-- Alternative implementation:
--   height{n = n}{L = L}{N = N} = FixedTree-induction 𝟎 (rec{w = n}) where
--     -- Note: The return type is equal to `RaiseType.repeat(L) ℕ ⇉ ℕ`
--     rec : ∀{w} → (a : N) → (c : (FixedTree(n) L N) ^ w) → RaiseType.from-[^] (Raise.map{w} (const ℕ)(c)) ⇉ ℕ
--     rec {w = 0}       _  _         = 1
--     rec {w = 1}       _  _       n = 𝐒(n)
--     rec {w = 𝐒(𝐒(w))} a  (_ , c) n = Multi.compose(𝐒(w)) (max n) (rec{w = 𝐒(w)} a c)
{-# TERMINATING #-}
height : FixedTree(n) L N → ℕ
height (Leaf _)   = 𝟎
height (Node _ c) = 𝐒(Raise.foldᵣ(max ∘ height) 𝟎 c)

import Data.Tuple.Raiseᵣ.Functions as TupleRaiseᵣ
import Data.List.Functions as List

treesOfDepth : ℕ → FixedTree(n) L N → List(FixedTree(n) L N)
treesOfDepth 𝟎      tree       = tree ⊰ ∅
treesOfDepth (𝐒(_)) (Leaf _)   = ∅
treesOfDepth (𝐒(n)) (Node _ c) = TupleRaiseᵣ.foldᵣ((List._++_) ∘ treesOfDepth n) ∅ c
