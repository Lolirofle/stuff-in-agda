module Functional.PrimitiveRecursion{lvl} where

open import Data
open        Data.Tuple.Raiseᵣ
open import Functional
open import Numeral.Natural as Nat using (ℕ)
open import Type{lvl}

-- A primitive recursive function of type (Tⁿ → T)
data Function : ℕ → Type where
  -- Base cases
  Constant    : Function(0)
  Successor   : Function(1)
  Projection  : ∀{n : ℕ} → (i : ℕ) → Function(Nat.𝐒(n))

  -- Inductive cases
  Composition : ∀{m n : ℕ} → Function(n) → (Function(m) ^ n) → Function(m)
  Recursion   : ∀{n : ℕ} → Function(n) → Function(Nat.𝐒(Nat.𝐒(n))) → Function(Nat.𝐒(n))

module OperShortcut where
  pattern Zero          = Constant
  pattern Succ          = Successor
  pattern Comp n m f gs = Composition{m}{n}(f)(gs)

  -- P : (n : ℕ) → (i : ℕ) → Function(n)
  -- P n i = Projection{Nat.𝐏(n)}(i)
  pattern P n i = Projection{n}(i)

  -- Rec : (n : ℕ) → Function(Nat.𝐏(n)) → Function(Nat.𝐒(n)) → Function(n)
  -- Rec n f g = Recursion{Nat.𝐏(n)}(f)(g)
  pattern Rec n f g = Recursion{n}(f)(g)

data Primitive : Type where
  𝟎 : Primitive
  𝐒 : Primitive → Primitive

-- The semantics
{-# TERMINATING #-}
evaluate : ∀{n} → Function(n) → (Primitive ^ n) → Primitive
evaluate {_}               (Constant)                 _  = 𝟎
evaluate {_}               (Successor)                x  = 𝐒(x)
evaluate {Nat.𝐒(n)}        (Projection(i))            xs = nth{n}(i)(xs)
evaluate {_}               (Composition{_}{n}(f)(gs)) xs = evaluate f (map{n}(g ↦ evaluate g xs)(gs))
evaluate {Nat.𝐒(Nat.𝟎)}    (Recursion(f)(g)) (𝟎   )        = evaluate f Unit.unit
evaluate {Nat.𝐒(Nat.𝟎)}    (Recursion(f)(g)) (𝐒(n))        = evaluate g (n , evaluate (Recursion(f)(g)) (n))
evaluate {Nat.𝐒(Nat.𝐒(_))} (Recursion(f)(g)) (𝟎    , rest) = evaluate f (rest)
evaluate {Nat.𝐒(Nat.𝐒(_))} (Recursion(f)(g)) (𝐒(n) , rest) = evaluate g (n , evaluate (Recursion(f)(g)) (n , rest) , rest)

module testAddition where
  open OperShortcut
  open import Relator.Equals{lvl}{lvl}

  plus = Rec(Nat.𝐏(2)) (P(Nat.𝐏(1))(0)) (Comp(1)(3) (Succ) (P(Nat.𝐏(3))(1)))

  -- testPlus1 : evaluate plus(𝐒(𝐒(𝐒(𝐒(𝟎)))) , 𝐒(𝐒(𝟎))) ≡ 𝐒(𝐒(𝐒(𝐒(𝐒(𝐒(𝟎))))))
  -- testPlus1 = [≡]-intro

record Defs (T : Type) : Type where
  field
    prim : T → Primitive
    val  : Primitive → T

-- record Function (T : Type) : Type where
--   field
--     Constant    : T
--     Successor   : T → T
--     Projection  : (i : ℕ) → (T ^ i) → T
--     Composition : (i : ℕ) → (n : ℕ) → (((T ^ n) → T) ⨯ (((T ^ i) → T) ^ n)) → ((T ^ i) → T)
--     Recursion   : (i : ℕ) → (((T ^ i) → T) ⨯ (T ^ (𝐒(𝐒(i))))) → ((T ^ i) → T)
