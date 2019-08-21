module Functional.PrimitiveRecursion where

import      Lvl
open import Data
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Data.Tuple.Raiseᵣ
open import Functional
open import Numeral.Natural
open import Type{Lvl.𝟎}

-- A primitive recursive function of type (Tⁿ → T)
-- The syntax
data Function : ℕ → Type where
  -- Base cases
  Base        : Function(0)
  Successor   : Function(1)
  Projection  : ∀{n : ℕ} → (i : ℕ) → Function(𝐒(n))

  -- Inductive cases
  Composition : ∀{m n : ℕ} → Function(n) → (Function(m) ^ n) → Function(m)
  Recursion   : ∀{n : ℕ} → Function(n) → Function(𝐒(𝐒(n))) → Function(𝐒(n))

module OperShortcut where
  pattern Zero          = Base
  pattern Succ          = Successor
  pattern Comp n m f gs = Composition{m}{n}(f)(gs)

  P : (n : ℕ) → (i : ℕ) → Function(𝐒(𝐏(n)))
  P (𝟎)    i = Projection{𝟎}(i)
  P (𝐒(n)) i = Projection{n}(i)
  -- pattern P n i = Projection{n}(i)

  Rec : (n : ℕ) → Function(𝐏(n)) → Function(𝐒(𝐒(𝐏(n)))) → Function(𝐒(𝐏(n)))
  Rec (𝟎)    f g = Recursion{𝟎}(f)(g)
  Rec (𝐒(n)) f g = Recursion{n}(f)(g)
  -- pattern Rec n f g = Recursion{n}(f)(g)

  zero' = Comp(0)(1) (Zero) <>

Primitive : Type
Primitive = ℕ

-- The semantics
{-# TERMINATING #-} -- TODO: The case of Composition is non-terminating?
evaluate : ∀{n} → Function(n) → (Primitive ^ n) → Primitive
evaluate {𝟎}       (Base)                       <> = 𝟎
evaluate {𝐒(𝟎)}    (Successor)                  x  = 𝐒(x)
evaluate {𝐒(n)}    (Projection(i))              xs = index{_}{_}{n}(i)(xs)
evaluate {_}       (Composition{_}{n}(f)(gs))   xs = evaluate f (map{n}(g ↦ evaluate g xs)(gs))
evaluate {𝐒(𝟎)}    (Recursion(f)(g)) (𝟎)           = evaluate f <>
evaluate {𝐒(𝟎)}    (Recursion(f)(g)) (𝐒(n))        = evaluate g (n , evaluate (Recursion(f)(g)) (n))
evaluate {𝐒(𝐒(_))} (Recursion(f)(g)) (𝟎    , rest) = evaluate f (rest)
evaluate {𝐒(𝐒(_))} (Recursion(f)(g)) (𝐒(n) , rest) = evaluate g (n , (evaluate (Recursion(f)(g)) (n , rest) , rest))
