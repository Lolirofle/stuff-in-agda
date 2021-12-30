module Data.BinaryTree where

import      Lvl
open import Type

private variable ℓ ℓₗ ℓₙ : Lvl.Level
private variable N L : Type{ℓ}

data BinaryTree (L : Type{ℓₗ}) (N : Type{ℓₙ}) : Type{ℓₗ Lvl.⊔ ℓₙ} where
  Leaf : L → BinaryTree L N
  Node : N → BinaryTree L N → BinaryTree L N → BinaryTree L N

elim : (P : BinaryTree L N → Type{ℓ}) → ((l : L) → P(Leaf l)) → (∀{tl tr} → (n : N) → (pl : P(tl)) → (pr : P(tr)) → P(Node n tl tr)) → ((t : BinaryTree L N) → P(t))
elim P pl pn (Leaf l)     = pl l
elim P pl pn (Node n l r) = pn n (elim P pl pn l) (elim P pl pn r)
