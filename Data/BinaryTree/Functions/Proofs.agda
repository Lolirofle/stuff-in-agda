module Data.BinaryTree.Functions.Proofs where

open import Data
open import Data.BinaryTree
open import Data.BinaryTree.Functions
open import Data.Boolean.Operators
open        Data.Boolean.Operators.Programming
open import Data.Boolean.Stmt
open import Data.Boolean.Stmt.Logic
open import Data.Option.Functions as Option
open import Functional as Fn using (_∘_)
import      Lvl
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Function.Domain
import      Structure.Function.Names as Names
open import Structure.Operator
open import Structure.Operator.Properties
open import Syntax.Implication
open import Syntax.Transitivity
open import Type

private variable ℓ ℓᵢ ℓₗ ℓₙ ℓₒ : Lvl.Level
private variable N N₁ N₂ L T A B C : Type{ℓ}
private variable id : T
private variable f : A → B
private variable _▫_ _▫ₗ_ _▫ₙ_ : A → B → C
private variable t : BinaryTree L N
private variable n : ℕ

foldInOrderDepthFirst-of-rotateₗ₀ : foldInOrderDepthFirst(_▫ₙ_)(_▫ₗ_) id (rotateₗ₀ t) ≡ foldInOrderDepthFirst(_▫ₙ_)(_▫ₗ_) id t
foldInOrderDepthFirst-of-rotateₗ₀ {t = Leaf x}                  = [≡]-intro
foldInOrderDepthFirst-of-rotateₗ₀ {t = Node x l (Leaf y)}       = [≡]-intro
foldInOrderDepthFirst-of-rotateₗ₀ {t = Node x l (Node y rl rr)} = [≡]-intro

foldInOrderDepthFirst-of-rotateᵣ₀ : foldInOrderDepthFirst(_▫ₙ_)(_▫ₗ_) id (rotateᵣ₀ t) ≡ foldInOrderDepthFirst(_▫ₙ_)(_▫ₗ_) id t
foldInOrderDepthFirst-of-rotateᵣ₀ {t = Leaf x}                  = [≡]-intro
foldInOrderDepthFirst-of-rotateᵣ₀ {t = Node x (Leaf y) r}       = [≡]-intro
foldInOrderDepthFirst-of-rotateᵣ₀ {t = Node x (Node y ll lr) r} = [≡]-intro

{-
isHeightPerfect-perfectHeight : IsTrue(isHeightPerfect n t) ↔ (perfectHeight t ≡ Some(n))
isHeightPerfect-perfectHeight = {!!} where
  left : IsTrue(isHeightPerfect n t) ← (perfectHeight t ≡ Some(n))
  left{n = n}{t = Leaf a} [≡]-intro = <>
  left {n = 𝟎} {t = Node a l r} p = {!!}
  left {n = 𝐒 n} {t = Node a l r} p = IsTrue.[∧]-intro (left{n = n}{t = l} {!!}) (left{n = n}{t = r} {!!})
  
  right : IsTrue(isHeightPerfect n t) → (perfectHeight t ≡ Some(n))
-}

size-of-perfect-binary-tree : IsTrue(isHeightPerfect n t) → (𝐒(size t) ≡ 2 ^ n)
size-of-perfect-binary-tree {𝟎} {t = Leaf _} p = [≡]-intro
size-of-perfect-binary-tree {𝐒 n} {t = Node a l r} p =
  • (p ⇒
    IsTrue(isHeightPerfect n l && isHeightPerfect n r) ⇒-[ IsTrue.[∧]-elimₗ ]
    IsTrue(isHeightPerfect n l)                        ⇒-[ size-of-perfect-binary-tree{n}{t = l} ]
    𝐒(size l) ≡ 2 ^ n                                  ⇒-end
  )
  • (p ⇒
    IsTrue(isHeightPerfect n l && isHeightPerfect n r) ⇒-[ IsTrue.[∧]-elimᵣ ]
    IsTrue(isHeightPerfect n r)                        ⇒-[ size-of-perfect-binary-tree{n}{t = r} ]
    𝐒(size r) ≡ 2 ^ n                                  ⇒-end
  )
  ⇒₂-[(\pl pr →
    𝐒(size(Node a l r))     🝖[ _≡_ ]-[]
    𝐒(𝐒(size(l) + size(r))) 🝖[ _≡_ ]-[]
    𝐒(size(l)) + 𝐒(size(r)) 🝖[ _≡_ ]-[ congruence₂(_+_) pl pr ]
    (2 ^ n) + (2 ^ n)       🝖[ _≡_ ]-[]
    (2 ^ n) ⋅ 2             🝖[ _≡_ ]-[ commutativity(_⋅_) {2 ^ n}{2} ]
    2 ⋅ (2 ^ n)             🝖[ _≡_ ]-[]
    2 ^ 𝐒(n)                🝖-end
  )]
  𝐒(size(Node a l r))  ≡ 2 ^ 𝐒(n) ⇒-end

numberOfLeaves-size-of-perfect-binary-tree : IsTrue(isHeightPerfect n t) → (numberOfLeaves t ≡ 𝐒(size t))
numberOfLeaves-size-of-perfect-binary-tree {𝟎}   {t = Leaf _}     p = [≡]-intro
numberOfLeaves-size-of-perfect-binary-tree {𝐒 n} {t = Node a l r} p =
  • (p ⇒
    IsTrue(isHeightPerfect n l && isHeightPerfect n r) ⇒-[ IsTrue.[∧]-elimₗ ]
    IsTrue(isHeightPerfect n l)                        ⇒-[ numberOfLeaves-size-of-perfect-binary-tree{n}{t = l} ]
    numberOfLeaves l ≡ 𝐒(size l)                       ⇒-end
  )
  • (p ⇒
    IsTrue(isHeightPerfect n l && isHeightPerfect n r) ⇒-[ IsTrue.[∧]-elimᵣ ]
    IsTrue(isHeightPerfect n r)                        ⇒-[ numberOfLeaves-size-of-perfect-binary-tree{n}{t = r} ]
    numberOfLeaves r ≡ 𝐒(size r)                       ⇒-end
  )
  ⇒₂-[(\pl pr →
    numberOfLeaves(Node a l r)          🝖[ _≡_ ]-[]
    numberOfLeaves l + numberOfLeaves r 🝖[ _≡_ ]-[ congruence₂(_+_) pl pr ]
    𝐒(size l) + 𝐒(size r)               🝖[ _≡_ ]-[]
    𝐒(𝐒(size l + size r))               🝖[ _≡_ ]-[]
    𝐒(size(Node a l r))                 🝖-end
  )]
  numberOfLeaves(Node a l r) ≡ 𝐒(size(Node a l r)) ⇒-end

rotateₗ-rotateᵣ-inverse : Option.partialMap Unit (Option.partialMap Unit (_≡ t) ∘ rotateₗ) (rotateᵣ t)
rotateₗ-rotateᵣ-inverse {t = Leaf _}                = <>
rotateₗ-rotateᵣ-inverse {t = Node _ (Leaf _) _}     = <>
rotateₗ-rotateᵣ-inverse {t = Node _ (Node _ _ _) _} = [≡]-intro

rotateᵣ-rotateₗ-inverse : Option.partialMap Unit (Option.partialMap Unit (_≡ t) ∘ rotateᵣ) (rotateₗ t)
rotateᵣ-rotateₗ-inverse {t = Leaf _}                = <>
rotateᵣ-rotateₗ-inverse {t = Node _ _ (Leaf _)}     = <>
rotateᵣ-rotateₗ-inverse {t = Node _ _ (Node _ _ _)} = [≡]-intro

instance
  flip-involution : Involution(flip{L = L}{N = N})
  flip-involution = intro p where
    p : Names.Involution(flip)
    p {Leaf a}     = [≡]-intro
    p {Node a l r} =
      (flip ∘ flip)(Node a l r)            🝖[ _≡_ ]-[]
      flip(Node a (flip r) (flip l))       🝖[ _≡_ ]-[]
      Node a (flip(flip l)) (flip(flip r)) 🝖[ _≡_ ]-[ congruence₂(Node a) (p{l}) (p{r}) ]
      Node a l r                           🝖-end

open import Logic.Propositional
open import Numeral.Natural.Function
open import Numeral.Natural.Function.Proofs
open import Numeral.Natural.Oper.Proofs.Order
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Proofs

size-maximum : (size(t) < 2 ^ height(t))
size-maximum {t = Leaf _}     = succ(_≤_.min)
size-maximum {t = Node a l r} =
  𝐒(size(Node a l r))                                                 🝖[ _≤_ ]-[]
  𝐒(𝐒(size(l) + size(r)))                                             🝖[ _≤_ ]-[]
  𝐒(size(l)) + 𝐒(size(r))                                             🝖[ _≤_ ]-[ [≤]-with-[+] ⦃ size-maximum{t = l} ⦄ ⦃ size-maximum{t = r} ⦄ ]
  (2 ^ (height l)) + (2 ^ (height r))                                 🝖[ _≤_ ]-[ [≤]-with-[+]
    ⦃ [^]ₗ-growing (\()) ([∧]-elimₗ(max-order{height l}{height r})) ⦄
    ⦃ [^]ₗ-growing (\()) ([∧]-elimᵣ(max-order{height l}{height r})) ⦄
  ]
  (2 ^ (max(height l) (height r))) + (2 ^ (max(height l) (height r))) 🝖[ _≤_ ]-[]
  (2 ^ (max(height l) (height r))) ⋅ 2                                🝖[ _≡_ ]-[ commutativity(_⋅_) {2 ^ (max(height l) (height r))}{2} ]-sub
  2 ⋅ (2 ^ (max(height l) (height r)))                                🝖[ _≤_ ]-[]
  2 ^ (𝐒(max(height l) (height r)))                                   🝖[ _≤_ ]-[]
  2 ^ height(Node a l r)                                              🝖-end
