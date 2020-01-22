module Function.PrimitiveRecursion where

import      Lvl
open import Data
open import Data.ListSized
open import Functional
open import Numeral.Finite
open import Numeral.Natural
open import Syntax.Number
open import Type{Lvl.𝟎}

-- Function(n) is a syntactic representation of primitive recursive functions of type (ℕⁿ → ℕ).
-- The syntax
data Function : ℕ → Type where
  -- Base cases
  Base        : Function(0)
  Successor   : Function(1)
  Projection  : ∀{n : ℕ} → (i : 𝕟(n)) → Function(n)

  -- Inductive cases
  Composition : ∀{m n : ℕ} → Function(n) → List(Function(m))(n) → Function(m)
  Recursion   : ∀{n : ℕ} → Function(n) → Function(𝐒(𝐒(n))) → Function(𝐒(n))

module OperShortcut where
  pattern Zero          = Base
  pattern Succ          = Successor
  pattern Comp n m f gs = Composition{m}{n}(f)(gs)

  -- P : (n : ℕ) → (i : 𝕟(n)) → Function(𝐒(𝐏(n)))
  -- P (𝟎)    i      = Projection{𝟎}(i)
  -- P (𝐒(n)) 𝟎      = Projection{n}(𝟎)
  -- P (𝐒(n)) (𝐒(i)) = Projection{n}(i)

  -- Rec : (n : ℕ) → Function(𝐏(n)) → Function(𝐒(𝐒(𝐏(n)))) → Function(𝐒(𝐏(n)))
  -- Rec (𝟎)    f g = Recursion{𝟎}(f)(g)
  -- Rec (𝐒(n)) f g = Recursion{n}(f)(g)

  zero' = Comp(0)(1) (Zero) ∅

Primitive : Type
Primitive = ℕ

-- The semantics.
-- `Base` is interpreted as the constant 0.
-- `Successor` is interpreted as the successor function of ℕ.
-- `Projection{n}(i)` is interpreted as the projection of the i:th element of ℕⁿ.
-- `Composition(f)(gs)` is interpreted as generalized composition by using map on the arguments of a function.
--    Specifically (f ∘ (map gs)).
-- `Recursion(f)(g)` is interpreted as a "recursion constructor".
--    This is used to construct a function `r` in which the following holds:
--    • r(0   ,..xs) = f(..xs)
--    • r(𝐒(n),..xs) = g(n,r(n,..xs),..xs)
evaluate : ∀{n} → Function(n) → List(Primitive)(n) → Primitive
evaluate {𝟎}    (Base)                     ∅             = 𝟎
evaluate {𝐒(𝟎)} (Successor)                (singleton x) = 𝐒(x)
evaluate {𝐒(n)} (Projection(i))            xs            = index(i)(xs)
evaluate {_}    (Composition{m}{n}(f)(gs)) xs            = evaluate f (mapper gs) where -- evaluate f (map(g ↦ evaluate g xs)(gs))
  mapper : ∀{n} → List(Function(m))(n) → List(Primitive)(n)
  mapper ∅        = ∅
  mapper (g ⊰ gs) = (evaluate g xs) ⊰ (mapper gs)
evaluate {𝐒(_)} (Recursion(f)(g))          (𝟎    ⊰ xs)   = evaluate f xs
evaluate {𝐒(_)} (Recursion(f)(g))          (𝐒(n) ⊰ xs)   = evaluate g (n ⊰ (evaluate (Recursion(f)(g)) (n ⊰ xs) ⊰ xs))


Const : Function(0) → ∀{n} → Function(n)
Const(c) = Composition(c) ∅

-- TODO: Would encoding pairs make this easier to implement (e.g. the Cantor Pairing Function?
--  This is used to construct a function `r` in which the following holds for its evaluation:
--  • r(0      ,..xs) = f(..xs)
--  • r(1      ,..xs) = g(..xs)
--  • r(𝐒(𝐒(n)),..xs) = h(n,r(𝐒(n),..xs),r(n,..xs),..xs)
-- Recursion₂ : ∀{n : ℕ} → Function(n) → Function(n) → Function(𝐒(𝐒(𝐒(n)))) → Function(𝐒(n))
-- Recursion₂{n} (f)(g)(h) = Composition(Projection(0)) (Helper ⊰ ∅) where
--   Recursion
-- 
--   Helper : Function(2)
--   Helper = 
-- 

module Arithmetic where -- TODO: Prove that these are correct by `evaluate`
  Zero = Base

  Number : ℕ → Function(0)
  Number(𝟎)    = Zero
  Number(𝐒(n)) = Composition(Successor) (Number(n) ⊰ ∅)

  Swap₂ : Function(2) → Function(2)
  Swap₂(f) = Composition(f) (Projection(1) ⊰ Projection(0) ⊰ ∅)

  -- Addition (+) in ℕ.
  -- It describes the following function:
  --   evaluate(Addition)[𝟎   ,b] = 𝟎
  --   evaluate(Addition)[𝐒(a),b] = 𝐒(b)
  Addition : Function(2)
  Addition = Recursion(Projection(0)) (Composition Successor (Projection(1) ⊰ ∅))

  -- Multiplication (⋅) in ℕ.
  -- It describes the following function:
  --   evaluate(Multiplication)[𝟎   ,b] = 𝟎
  --   evaluate(Multiplication)[𝐒(a),b] = evaluate(Multiplication)[a,b] + b
  Multiplication : Function(2)
  Multiplication = Recursion(Const(Zero)) (Composition Addition (Projection(1) ⊰ Projection(2) ⊰ ∅))

  -- Exponentiation (^) in ℕ.
  -- It describes the following function:
  --   evaluate(Exponentiation)[𝟎   ,b] = 1
  --   evaluate(Exponentiation)[𝐒(a),b] = evaluate(Exponentiation)[a,b] ⋅ b
  Exponentiation : Function(2)
  Exponentiation = Recursion(Const(Zero)) (Composition Multiplication (Projection(1) ⊰ Projection(2) ⊰ ∅))

  -- Factorial (!) in ℕ.
  -- It describes the following function:
  --   evaluate(Factorial)[𝟎   ] = 1
  --   evaluate(Factorial)[𝐒(a)] = 𝐒(a) ⋅ evaluate(Factorial)[a,b]
  Factorial : Function(1)
  Factorial = Recursion(Number(1)) (Composition Multiplication ((Composition Successor (Projection(0) ⊰ ∅)) ⊰ Projection(1) ⊰ ∅))

  -- Predecessor (𝐏) in ℕ.
  -- It describes the following function:
  --   evaluate(Predecessor)[𝟎   ] = 𝟎
  --   evaluate(Predecessor)[𝐒(a)] = a
  Predecessor : Function(1)
  Predecessor = Recursion(Zero) (Projection(0))

  -- Monus/Cut-off minus (−₀) in ℕ.
  -- It describes the following function:
  --   evaluate(Monus)[b,𝟎   ] = b
  --   evaluate(Monus)[b,𝐒(a)] = 𝐏(evaluate(Monus)[b,a])
  Monus : Function(2)
  Monus = Swap₂(Recursion(Projection(0)) (Composition Predecessor (Projection(1) ⊰ ∅)))

  -- Maximum (max) of ℕ² in ℕ.
  -- It describes the following function:
  --   evaluate(Max)[a,b] = a + (b −₀ a)
  Max : Function(2)
  Max = Composition(Addition) (Projection(0) ⊰ Swap₂(Monus) ⊰ ∅)

  -- Minimum (min) of ℕ² in ℕ.
  -- It describes the following function:
  --   evaluate(Min)[a,b] = (a + b) −₀ max(a,b)
  Min : Function(2)
  Min = Composition(Monus) (Addition ⊰ Max ⊰ ∅)

  -- It describes the following function:
  --   evaluate(Distance)[a,b] = max(x −₀ y , y −₀ x)
  Distance : Function(2)
  Distance = Composition(Addition) (Monus ⊰ Swap₂(Monus) ⊰ ∅)

  -- It describes the following function:
  --   evaluate(IsZero)[𝟎]    = 1
  --   evaluate(IsZero)[𝐒(_)] = 0
  IsZero : Function(1)
  IsZero = Recursion(Number(1)) (Const(Zero))

  -- It describes the following function:
  --   evaluate(IsZero)[𝟎]    = 0
  --   evaluate(IsZero)[𝐒(_)] = 1
  IsNonZero : Function(1)
  IsNonZero = Composition(IsZero) (IsZero ⊰ ∅)

  Eq : Function(2)
  Eq = Composition(IsZero) (Distance ⊰ ∅)

  -- It describes the following function:
  --   evaluate(Fibonacci)[𝟎]    = 0
  --   evaluate(Fibonacci)[𝐒(_)] = 1
  -- Fibonacci : Function(1)
  -- Fibonacci = Composition(Projection(0)) (Fib ⊰ ∅) where
  --   Fib : Function(2)
  --   Fib = 

-- TODO: http://www.reluctantm.com/gcruttw/teaching/cpsc513.W2010/A3Solutions.pdf
-- TODO: http://ii.fmph.uniba.sk/cl/courses/1-AIN-625-lpp/0910zs/ln/doc/ch_p_gd.pdf
-- TODO: https://proofwiki.org/wiki/Equality_Relation_is_Primitive_Recursive
