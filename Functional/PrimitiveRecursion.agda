module Functional.PrimitiveRecursion where

import      Level as Lvl
open import Data
open        Data.Tuple.Raiseᵣ
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
{-# TERMINATING #-}
evaluate : ∀{n} → Function(n) → (Primitive ^ n) → Primitive
evaluate {𝟎}       (Base)                       <> = 𝟎
evaluate {𝐒(𝟎)}    (Successor)                  x  = 𝐒(x)
evaluate {𝐒(n)}    (Projection(i))              xs = nth{n}(i)(xs)
evaluate {_}       (Composition{_}{n}(f)(gs))   xs = evaluate f (map{n}(g ↦ evaluate g xs)(gs))
evaluate {𝐒(𝟎)}    (Recursion(f)(g)) (𝟎)           = evaluate f <>
evaluate {𝐒(𝟎)}    (Recursion(f)(g)) (𝐒(n))        = evaluate g (n , evaluate (Recursion(f)(g)) (n))
evaluate {𝐒(𝐒(_))} (Recursion(f)(g)) (𝟎    , rest) = evaluate f (rest)
evaluate {𝐒(𝐒(_))} (Recursion(f)(g)) (𝐒(n) , rest) = evaluate g (n , (evaluate (Recursion(f)(g)) (n , rest) , rest))

module testDefinitions where
  open        OperShortcut
  import      Numeral.Natural.Oper     as Nat
  import      Numeral.Natural.Function as Nat
  open import Relator.Equals{Lvl.𝟎}{Lvl.𝟎}

  plus   = Rec(2) (P(1)(0)) (Comp(1)(3) (Succ) (P(3)(1)))
  pred   = Rec(1) (Zero) (P(2)(0))
  monus  = Comp(2)(2) (Rec(2) (P(1)(0)) (Comp(1)(3) (pred) (P(3)(1)))) (P(2)(1) , P(2)(0))
  max    = Comp(2)(2) (plus) (P(2)(0) , Comp(2)(2) (monus) (P(2)(1) , P(2)(0)))
  min    = Comp(2)(2) (monus) (plus , max)
  iszero = Rec(1) (Comp(1)(0) (Succ) (Zero)) (Comp(0)(2) (Zero) <>)
  const3 = Comp(1)(0) (Succ) (Comp(1)(0) (Succ) (Comp(1)(0) (Succ) (Zero)))

  -- testPlus1 : evaluate plus(4 , 2) ≡ 6
  -- testPlus1 = [≡]-intro

  -- testMonus1 : evaluate monus(4 , 0) ≡ 4
  -- testMonus1 = [≡]-intro

  -- testMonus2 : evaluate monus(0 , 4) ≡ 0
  -- testMonus2 = [≡]-intro

  -- testMonus3 : evaluate monus(10 , 2) ≡ 8
  -- testMonus3 = [≡]-intro

  -- testMonus4 : evaluate monus(2 , 10) ≡ 0
  -- testMonus4 = [≡]-intro

  -- testMin1 : evaluate min(3 , 2) ≡ Nat.min(3)(2)
  -- testMin1 = [≡]-intro

  proofPred : ∀{n} → evaluate pred(n) ≡ 𝐏(n)
  proofPred{𝟎}    = [≡]-intro
  proofPred{𝐒(n)} = [≡]-intro

  proofPlus : ∀{a b} → evaluate plus(b , a) ≡ (a Nat.+ b)
  proofPlus{𝟎}   {𝟎}    = [≡]-intro
  proofPlus{𝐒(_)}{𝟎}    = [≡]-intro
  proofPlus{a}   {𝐒(b)} = [≡]-with-[ 𝐒 ] (proofPlus{a}{b})

  is-zero : ℕ → ℕ
  is-zero(0) = 1
  is-zero(_) = 0

  proofIsZero : ∀{n} → evaluate iszero(n) ≡ is-zero(n)
  proofIsZero{𝟎}    = [≡]-intro
  proofIsZero{𝐒(_)} = [≡]-intro

  proofMonus : ∀{a} → evaluate monus(a , 𝟎) ≡ (a Nat.−₀ 𝟎)
  proofMonus{𝟎} = [≡]-intro
  proofMonus{_} = [≡]-intro

  proofMax : ∀{a} → evaluate max(0 , a) ≡ Nat.max(a)(0)
  proofMax{𝟎}    = [≡]-intro
  proofMax{𝐒(_)} = [≡]-intro

  -- proofMin : ∀{a} → evaluate min(0 , a) ≡ Nat.min(a)(0)
  -- proofMin{𝟎}    = [≡]-intro
  -- proofMin{𝐒(_)} = [≡]-intro
