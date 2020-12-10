-- Alternating addition (Also called the Calkin-Wilf tree representation of the rationals).
-- One bijective representation of ℚ. That is, every rational number is appearing exactly once in this representation (TODO: Some proof would be nice).
module Numeral.Rational.AlterAdd where

import      Lvl
open import Data
open import Data.Boolean
open import Logic.Propositional
open import Numeral.Natural             as ℕ
import      Numeral.Natural.Oper        as ℕ
import      Numeral.Natural.Oper.Comparisons as ℕ
open import Numeral.PositiveInteger      as ℕ₊
open import Numeral.PositiveInteger.Oper as ℕ₊
open import Numeral.Integer using (ℤ)
open import Syntax.Number
open import Type

module Test1 where
  data Tree : ℕ₊ → ℕ₊ → Type{Lvl.𝟎} where
    intro : Tree(1)(1)
    left  : ∀{x y} → Tree(x)(y) → Tree(x) (y ℕ₊.+ x)
    right : ∀{x y} → Tree(x)(y) → Tree(x ℕ₊.+ y) (y)

  -- Tree-cancellationₗ : ∀{x₁ x₂ y} → (Tree x₁ y ≡ Tree x₂ y) → (x₁ ≡ x₂)

  {- TODO: Is there an algorithm that determines the path to every rational in this tree? Maybe the division algorithm:
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
  If this is the case, then just represent the tree by: (Tree = List(Bool)) or (Tree = List(Either ℕ ℕ)) or (Tree = List(ℕ)) ?-}

  {-
  open import Data.Option
  Tree-construct : (x : ℕ₊) → (y : ℕ₊) → Tree(x)(y)
  Tree-construct ℕ₊.𝟏        ℕ₊.𝟏         = intro
  Tree-construct ℕ₊.𝟏        (𝐒 y)        = left(Tree-construct ℕ₊.𝟏 y)
  Tree-construct (𝐒 x)       ℕ₊.𝟏         = right(Tree-construct x ℕ₊.𝟏)
  Tree-construct(x@(ℕ₊.𝐒 _)) (y@(ℕ₊.𝐒 _)) with (x −₀ y)
  ... | Some z = {!right(Tree-construct(z)(y))!}
  ... | None   = {!left (Tree-construct(x)(y ℕ.−₀ x))!}
  -}

  -- _+_ : Tree(a₁)(b₁) → Tree(a₂)(b₂) → 
  -- _⋅_ : Tree(a₁)(b₁) → Tree(a₂)(b₂) → 

  data ℚ : Type{Lvl.𝟎} where
    𝟎  : ℚ
    _/₋_ : (x : ℕ₊) → (y : ℕ₊) → ⦃ _ : Tree(x)(y) ⦄ → ℚ
    _/₊_ : (x : ℕ₊) → (y : ℕ₊) → ⦃ _ : Tree(x)(y) ⦄ → ℚ

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

  {-
  from-ℕ : ℕ → ℚ
  from-ℕ(𝟎)    = 𝟎
  from-ℕ(𝐒(n)) = (𝐒(n) /₊ 1) where
    instance
      f : (n : ℕ) → Tree(𝐒(n))(1)
      f(𝟎)    = Tree-intro
      f(𝐒(n)) = Tree-right(f(n))
  -}

  {-
  floor : ℚ → ℕ
  floor(x / y) = x ℕ.⌊/⌋ y

  ceil : ℚ → ℕ
  ceil(x / y) = x ℕ.⌈/⌉ y
  -}

{-
module Test2 where
  open import Data.Tuple as Tuple using (_⨯_ ; _,_)
  open import Functional

  data Tree : Type{Lvl.𝟎} where
    intro : Tree
    left  : Tree → Tree
    right : Tree → Tree

  Tree-quotient : Tree → (ℕ ⨯ ℕ)
  Tree-quotient intro                                    = (1       , 1      )
  Tree-quotient (left  t) with (x , y) ← Tree-quotient t = (x       , x ℕ.+ y)
  Tree-quotient (right t) with (x , y) ← Tree-quotient t = (x ℕ.+ y , y      )

  Tree-denominator : Tree → ℕ
  Tree-denominator = Tuple.right ∘ Tree-quotient

  Tree-numerator : Tree → ℕ
  Tree-numerator = Tuple.left ∘ Tree-quotient
-}
