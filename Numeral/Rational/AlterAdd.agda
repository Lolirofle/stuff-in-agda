-- Alternating addition (Also called the Calkin-Wilf tree representation of the rationals).
-- One bijective representation of ℚ. That is, every rational number is appearing exactly once in this representation (TODO: Some proof would be nice).
module Numeral.Rational.AlterAdd where

open import Data.Boolean
open import Logic.Propositional
open import Numeral.Natural             as ℕ
import      Numeral.Natural.Oper        as ℕ
import      Numeral.Natural.BooleanOper as ℕ
import      Numeral.Integer
open        Numeral.Integer             using (ℤ)

data Tree : ℕ → ℕ → Set where
  Tree-intro : Tree(1)(1)
  Tree-left  : ∀{x y} → Tree(x)(y) → Tree(x) (x ℕ.+ y)
  Tree-right : ∀{x y} → Tree(x)(y) → Tree(x ℕ.+ y) (y)
{-# INJECTIVE Tree #-}

postulate Tree-zeroₗ : ∀{x} → ¬(Tree(0)(x))
postulate Tree-zeroᵣ : ∀{x} → ¬(Tree(x)(0))

-- TODO: Is there an algorithm that determines the path to every rational in this tree?
{-
Like the division algorithm:
R6 (14928,2395)
L4 (558,2395) 14928−2395⋅6 = 558
R3 (558,163) 2395−558⋅4 = 163
L2 (69,163) 558−163⋅3 = 69
R2 (69,25) 163−69⋅2 = 25
L1 (19,25) 69−25⋅2 = 19
R3 (19,6) 25-19 = 6
L5 (1,6) 19-6⋅3 = 1
In (1,1) 6−1⋅5 = 1
f(R$R$R$R$R$R $ L$L$L$L $ R$R$R $ L$L $ R$R $ L $ R$R$R $ L$L$L$L$L $ Init)


postulate TODO : ∀{a} → a
Tree-construction-algorithm : (x : ℕ) → (y : ℕ) → Tree(x)(y)
Tree-construction-algorithm(0)(_) = TODO
Tree-construction-algorithm(_)(0) = TODO
Tree-construction-algorithm(1)(1) = Tree-intro
Tree-construction-algorithm(x)(y) with (x ℕ.≤? y) -- TODO: Prove that ℕ.≤? is both ComputablyDecidable and Decidable
... | 𝑇 = Tree-left (Tree-construction-algorithm(x)(y ℕ.−₀ x))
... | 𝐹 = Tree-right(Tree-construction-algorithm(x ℕ.−₀ y)(y))
-}
-- _+_ : Tree(a₁)(b₁) → Tree(a₂)(b₂) → 
-- _⋅_ : Tree(a₁)(b₁) → Tree(a₂)(b₂) → 

data ℚ : Set where
  𝟎  : ℚ
  _/₋_ : (x : ℕ) → (y : ℕ) → ⦃ _ : Tree(x)(y) ⦄ → ℚ
  _/₊_ : (x : ℕ) → (y : ℕ) → ⦃ _ : Tree(x)(y) ⦄ → ℚ

{-
_/_ : (x : ℤ) → (y : ℤ) → ℚ
_/_ 𝟎 _ = 𝟎
_/_ _ 𝟎 = 𝟎
_/_ (𝐒(x)) (𝐒(y)) with sign(x) ⋅ sign(y)
... | [−] = (x /₋ y) ⦃ Tree-construction-algorithm(x)(y) ⦄
... | [+] = (x /₊ y) ⦃ Tree-construction-algorithm(x)(y) ⦄
-}

{-
a₁/(a₁+b₁)
(a₂+b₂)/b₂
-}

from-ℕ : ℕ → ℚ
from-ℕ(𝟎)    = 𝟎
from-ℕ(𝐒(n)) = (𝐒(n) /₊ 1) where
  instance
    f : (n : ℕ) → Tree(𝐒(n))(1)
    f(𝟎)    = Tree-intro
    f(𝐒(n)) = Tree-right(f(n))

{-
floor : ℚ → ℕ
floor(x / y) = x ℕ.⌊/⌋ y

ceil : ℚ → ℕ
ceil(x / y) = x ℕ.⌈/⌉ y
-}
