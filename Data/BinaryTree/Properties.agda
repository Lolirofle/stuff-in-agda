module Data.BinaryTree.Properties where

import      Lvl
open import Data hiding (empty)
open import Data.BinaryTree
open import Data.Boolean
open import Functional as Fn
open import Logic.Propositional
open import Numeral.Natural
open import Type

private variable ℓ ℓᵢ ℓₗ ℓₙ ℓₒ : Lvl.Level
private variable n : ℕ
private variable N N₁ N₂ L T A B : Type{ℓ}

-- A tree is full when every node has no or all children.
data Full {L : Type{ℓₗ}}{N : Type{ℓₙ}} : BinaryTree L N → Type{ℓₗ Lvl.⊔ ℓₙ} where
  leaf   : ∀{l} → Full(Leaf l)
  single : ∀{a}{l₁ l₂} → Full(Node a (Leaf l₁) (Leaf l₂))
  step   : ∀{al ar a}{cll clr crl crr} → Full(Node al cll clr) → Full(Node ar crl crr) → Full(Node a (Node al cll clr) (Node ar crl crr))

-- A tree is perfect at depth `n` when all leaves are at height `n`.
-- In other words, a tree is perfect when all leaves are at the same height.
data Perfect {L : Type{ℓₗ}}{N : Type{ℓₙ}} : BinaryTree L N → ℕ → Type{ℓₗ Lvl.⊔ ℓₙ} where
  leaf : ∀{l} → Perfect(Leaf l)(𝟎)
  step : ∀{a}{l r}{h} → Perfect(l)(h) → Perfect(r)(h) → Perfect(Node a l r)(𝐒(h))

data Complete {L : Type{ℓₗ}}{N : Type{ℓₙ}} : BinaryTree L N → ℕ → Bool → Type{ℓₗ Lvl.⊔ ℓₙ} where
  perfect-leaf : ∀{l} → Complete(Leaf l)(𝟎)(𝑇)
  imperfect-leaf : ∀{l} → Complete(Leaf l)(𝐒(𝟎))(𝐹)
  step₀ : ∀{a}{l r}{h} → Complete(l)(h)(𝐹) → Complete(r)(h)(𝐹) → Complete(Node a l r)(𝐒(h))(𝐹)
  step₁ : ∀{a}{l r}{h} → Complete(l)(h)(𝑇) → Complete(r)(h)(𝐹) → Complete(Node a l r)(𝐒(h))(𝐹)
  step₂ : ∀{a}{l r}{h} → Complete(l)(h)(𝑇) → Complete(r)(h)(𝑇) → Complete(Node a l r)(𝐒(h))(𝑇)

data DepthOrdered {L : Type{ℓₗ}}{N : Type{ℓₙ}} (_≤_ : N → N → Type{ℓₒ}) : BinaryTree L N → Type{ℓₗ Lvl.⊔ ℓₙ Lvl.⊔ ℓₒ} where
  leaf : ∀{l} → DepthOrdered(_≤_)(Leaf l)
  step : ∀{a}{l₁ l₂} → DepthOrdered(_≤_)(Node a (Leaf l₁) (Leaf l₂))
  stepₗ : ∀{a al ar}{l}{rl rr} → (a ≤ al) → DepthOrdered(_≤_)(Node al rl rr)
                                          → DepthOrdered(_≤_)(Node a (Leaf l) (Node ar rl rr))
  stepᵣ : ∀{a al ar}{l}{ll lr} → (a ≤ ar) → DepthOrdered(_≤_)(Node ar ll lr)
                                          → DepthOrdered(_≤_)(Node a (Node al ll lr) (Leaf l))
  stepₗᵣ : ∀{a al ar}{ll lr rl rr} → (a ≤ al) → DepthOrdered(_≤_)(Node al ll lr)
                                   → (a ≤ ar) → DepthOrdered(_≤_)(Node ar rl rr)
                                   → DepthOrdered(_≤_)(Node a (Node al ll lr) (Node ar rl rr))

Heap : ∀{L : Type{ℓₗ}}{N : Type{ℓₙ}} → (N → N → Type{ℓₒ}) → BinaryTree L N → ℕ → Bool → Type
Heap(_≤_) tree height perfect = DepthOrdered(_≤_)(tree) ∧ Complete(tree)(height)(perfect)
