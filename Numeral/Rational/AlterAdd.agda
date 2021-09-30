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

module Test0 where
  import      Data.Boolean.Operators
  open        Data.Boolean.Operators.Programming
  open import Data.Tuple as Tuple using (_⨯_ ; _,_)
  open import Data.List
  import      Data.List.Functions as List
  open import Functional
  open import Numeral.Natural.Inductions
  open import Numeral.Natural.Oper.FlooredDivision
  open import Numeral.Natural.Oper.Modulo
  open import Numeral.Natural.Oper.Modulo.Proofs
  open import Numeral.Natural.Oper.Proofs.Order
  open import Numeral.Natural.Relation
  open import Numeral.Natural.Relation.Order
  open import Numeral.Natural.Relation.Order.Proofs
  open import Structure.Relator.Ordering

  -- A binary representation of the rational numbers.
  -- Source: This is based on the Calkin-Wilf tree.
  ℚ₊ = List(Bool)
  module ℚ₊ where
    -- Converts this representation to the standard quotient representation of rational numbers using pairs.
    -- Haskell implementation:
    --   toPair :: QPos -> (Int,Int)
    --   toPair = foldr(\b (x,y) -> if b then (x + y , y) else (x , y + x)) (1,1)
    toPair : ℚ₊ → (ℕ ⨯ ℕ)
    toPair = List.foldᵣ(\b (x , y) → if b then (x ℕ.+ y , y) else (x , y ℕ.+ x)) (1 , 1)

    -- Converts from the standard quotient representation of rational numbers using pairs to this representation.
    -- Note that this operation is lossy if the given pair is not coprime.
    -- Haskell implementation:
    --   fromPair :: (Int,Int) -> QPos
    --   fromPair(x,y) = case compare x y of
    --     LT -> False : fromPair(x , y - x)
    --     EQ -> []
    --     GT -> True : fromPair(x - y , y)
    fromPair : (x : ℕ) → (y : ℕ) → ⦃ pos-x : Positive(x) ⦄ → ⦃ pos-y : Positive(y) ⦄ → ℚ₊
    fromPair x y = Strict.Properties.wellfounded-recursion(_<_) {P = \x → ⦃ pos-x : Positive(x) ⦄ → ℚ₊} (\x prev-x → Strict.Properties.wellfounded-recursion(_<_) {P = \y → ⦃ pos-y : Positive(y) ⦄ → ℚ₊} (f x prev-x) y) x where
      f : (x : ℕ) → ((i : ℕ) ⦃ _ : i < x ⦄ → ⦃ pos : Positive(i) ⦄ → ℚ₊) → ⦃ pos-x : Positive(x) ⦄
        → (y : ℕ) → ((i : ℕ) ⦃ _ : i < y ⦄ → ⦃ pos : Positive(i) ⦄ → ℚ₊) → ⦃ pos-y : Positive(y) ⦄
        → ℚ₊
      f x prev-x y prev-y with [<]-trichotomy {x}{y}
      ... | [∨]-introₗ([∨]-introₗ lt) = 𝐹 ⊰ prev-y(y ℕ.−₀ x) ⦃ [−₀]-strictly-lesser ([≤]-predecessor lt) ⦄ ⦃ [↔]-to-[→] [−₀]-positive lt ⦄
      ... | [∨]-introₗ([∨]-introᵣ eq) = ∅
      ... | [∨]-introᵣ            gt  = 𝑇 ⊰ prev-x (x ℕ.−₀ y) ⦃ [−₀]-strictly-lesser ([≤]-predecessor gt) ⦄ ⦃ [↔]-to-[→] [−₀]-positive gt ⦄

    -- Reciprocal function of ℚ₊.
    ⅟ : ℚ₊ → ℚ₊
    ⅟ = List.map(!)

    ⅟ₙ : (n : ℕ) → ⦃ Positive(n) ⦄ → ℚ₊
    ⅟ₙ(𝐒(n)) = List.repeat 𝐹 n

    -- Example: n / 1
    fromℕ : (n : ℕ) → ⦃ Positive(n) ⦄ → ℚ₊
    fromℕ(𝐒(n)) = List.repeat 𝑇 n

    -- Example: n + (x / y) = ((n ⋅ y) + x) / y
    _+ₙ_ : ℕ → ℚ₊ → ℚ₊
    _+ₙ_ = List._++_ ∘ List.repeat 𝑇

    open import Numeral.Natural.Coprime
    open import Numeral.Natural.Coprime.Proofs
    open import Numeral.Natural.Oper.Proofs
    open import Relator.Equals.Proofs.Equiv
    open import Structure.Operator.Properties
    open import Structure.Relator
    open import Structure.Relator.Properties

    toPair-coprime : ∀{x} → Tuple.uncurry Coprime(toPair(x))
    toPair-coprime {∅}     = Coprime-of-1
    toPair-coprime {𝑇 ⊰ l} = let (x , y) = toPair l in substitute₂ₗ(Coprime) (commutativity(ℕ._+_) {y}{x}) (symmetry(Coprime) (Coprime-of-[+] (symmetry(Coprime) (toPair-coprime {l}))))
    toPair-coprime {𝐹 ⊰ l} = let (x , y) = toPair l in substitute₂ᵣ(Coprime) (commutativity(ℕ._+_) {x}{y}) (Coprime-of-[+] (toPair-coprime {l}))

    toPair-positive : ∀{x} → let (a , b) = toPair x in Positive(a) ∧ Positive(b)
    toPair-positive{∅}     = [∧]-intro <> <>
    toPair-positive{𝑇 ⊰ l} = let (pa , pb) = toPair-positive{l} in [∧]-intro ([↔]-to-[→] [+]-positive ([∨]-introₗ pa)) pb
    toPair-positive{𝐹 ⊰ l} = let (pa , pb) = toPair-positive{l} in [∧]-intro pa ([↔]-to-[→] [+]-positive ([∨]-introₗ pb))

  data ℚ : Type{Lvl.𝟎} where
    neg  : ℚ₊ → ℚ
    zero : ℚ
    pos  : ℚ₊ → ℚ

{-
(x + n*y) / y
x/y + n

x / (y + n*x)
1 / ((y + n*x) / x)
1 / (y/x + n)
-}

{-
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
-}
