module Data.FixedTree.Properties where

import      Lvl
open import Data using (Unit ; <>)
open import Data.Boolean
open import Data.FixedTree
open import Data.Tuple.Raise
import      Data.Tuple.Raiseᵣ.Functions as Raise
open import Functional as Fn
open import Logic.Propositional
open import Numeral.Finite
open import Numeral.Finite.Oper.Comparisons
open import Numeral.Natural
open import Type

private variable ℓ ℓᵢ ℓₗ ℓₙ ℓₒ : Lvl.Level
private variable n : ℕ
private variable N N₁ N₂ L T A B : Type{ℓ}

-- A tree is full when every node has no or all children.
data Full {L : Type{ℓₗ}}{N : Type{ℓₙ}}{n} : FixedTree(n) L N → Type{ℓₗ Lvl.⊔ ℓₙ} where
  leaf   : ∀{l} → Full(Leaf l)
  single : ∀{a}{l} → Full(Node a (Raise.repeat(n) (Leaf l))) -- TODO: All the leaves should not be forced to all have the same data
  step   : ∀{a : N}{ca : N ^ n}{cc : ((FixedTree(n) L N) ^ n) ^ n} → (∀{i : 𝕟(n)} → Full(Node (Raise.index i ca) (Raise.index i cc))) → Full(Node a (Raise.map₂{n} Node ca cc))
  -- step  : ∀{a : T}{ca : T ^ n}{cc : (FixedTree(n)(T) ^ n) ^ n} → Raise.reduceOrᵣ{n}(_⨯_) Unit (Raise.map₂(Full ∘₂ Node) ca cc) → Full(Node a (Raise.map₂{n} Node ca cc))

-- A tree is perfect at depth `n` when all leaves are at height `n`.
-- In other words, a tree is perfect when all leaves are at the same height.
data Perfect {L : Type{ℓₗ}}{N : Type{ℓₙ}}{n} : FixedTree(n) L N → ℕ → Type{ℓₗ Lvl.⊔ ℓₙ} where
  leaf : ∀{l} → Perfect(Leaf l)(𝟎)
  step : ∀{a}{c}{h} → (∀{i : 𝕟(n)} → Perfect(Raise.index i c)(h)) → Perfect(Node a c)(𝐒(h))

data Complete {L : Type{ℓₗ}}{N : Type{ℓₙ}}{n} : FixedTree(n) L N → ℕ → Bool → Type{ℓₗ Lvl.⊔ ℓₙ} where
  perfect-leaf : ∀{l} → Complete(Leaf l)(𝟎)(𝑇)
  imperfect-leaf : ∀{l} → Complete(Leaf l)(𝐒(𝟎))(𝐹)
  step : ∀{a}{c}{h}{t : 𝕟(n)} → (∀{i : 𝕟(n)} → Complete(Raise.index i c)(h)(i ≤? t)) → Complete(Node a c)(𝐒(h))(t ≤? maximum{n})

data DepthOrdered {L : Type{ℓₗ}}{N : Type{ℓₙ}} (_≤_ : N → N → Type{ℓₒ}) {n} : FixedTree(n) L N → Type{ℓₗ Lvl.⊔ ℓₙ Lvl.⊔ ℓₒ} where
  leaf : ∀{l} → DepthOrdered(_≤_)(Leaf l)
  step : ∀{p}{c : (FixedTree(n) L N) ^ n} → (∀{i : 𝕟(n)} → (\{(Leaf _) → Unit ; (Node a c) → (p ≤ a) ∧ DepthOrdered(_≤_)(Node a c)}) $ (Raise.index i c)) → DepthOrdered(_≤_)(Node p c)

Heap : ∀{L : Type{ℓₗ}}{N : Type{ℓₙ}} → (N → N → Type{ℓₒ}) → ∀{n} → FixedTree(n) L N → ℕ → Bool → Type
Heap(_≤_) tree height perfect = DepthOrdered(_≤_)(tree) ∧ Complete(tree)(height)(perfect)
