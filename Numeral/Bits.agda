module Numeral.Bits where

import      Lvl
open import Data.List
open import Data.Boolean hiding (elim)
open import Data.Option
open import Type

-- A formalization of the positional binary radix numeral system for the notation of numbers.
-- This representation is simple (using only common algebraic data types (`List`, `Option`, `Bool`)) and have a unique representation for each number (have a bijection to ℕ).
-- The head of the list is the least significant position of the number (the reverse of the usual positional notation of numbers).
-- Usually, a finite bit sequence like `List(Bool)` is used to represent numbers, but the problem is that there will be an infinite number of ways to represent any number by just repeating zeroes at the most significant position (for example [1], [1,0], [1,0,0], [1,0,0,0] are all just 1 (compare with the usual notation: 1, 01, 001, 0001) and [], [0], [0,0], [0,0,0] are all 0).
-- By interpreting the empty list as a sequence with 1 at the most significant position, all duplicate representations are gone.
-- Example of `Bits`:
--   None        represents 0₂.
--   Some ∅      represents 1₂.
--   Some(0 ⊰ ∅) represents 10₂.
--   Some(1 ⊰ ∅) represents 11₂.
--   Some(0 ⊰ 0 ⊰ ∅) represents 100₂.
--   Some(1 ⊰ 0 ⊰ ∅) represents 101₂.
--   Some(0 ⊰ 1 ⊰ ∅) represents 110₂.
--   Some(1 ⊰ 1 ⊰ ∅) represents 111₂.
-- Note: Special case of Numeral.FixedPositional for base 2.
Bits₊ = List Bool
Bits  = Option Bits₊

module Syntax where
  open import Data using (<>) public
  open import Data.Boolean.Numeral using (Bool-from-ℕ) public
  open import Syntax.Number public

  -- Ease of use syntax for Bits₊.
  -- Example:
  --   #1· 0 · 1 · 0 represents 1010₂.
  pattern #1· n = n ⊰ ∅
  pattern _·_ a b = b ⊰ a
  infixl 100 _·_

  -- Ease of use syntax for Bits.
  -- Example:
  --   + #𝟏· 0 · 1 · 0 represents 1010₂.
  pattern 𝟎 = None
  pattern +_ n = Some n
  infixl 10 +_

module Values where
  -- Representation of 1 using `Bits₊`.
  𝟏₊ : Bits₊
  𝟏₊ = ∅

  -- Representation of 2 using `Bits₊`.
  𝟐₊ : Bits₊
  𝟐₊ = 𝐹 ⊰ ∅

  -- Representation of 0 using `Bits`.
  𝟎 : Bits
  𝟎 = None

  -- Representation of 1 using `Bits`.
  𝟏 : Bits
  𝟏 = Some 𝟏₊

open import DependentFunctional using (_∘_)

module Bits₊ where
  -- Successor function of `Bits₊`.
  𝐒 : Bits₊ → Bits₊
  𝐒 ∅      = Values.𝟐₊
  𝐒(𝐹 ⊰ b) = 𝑇 ⊰ b
  𝐒(𝑇 ⊰ b) = 𝐹 ⊰ 𝐒(b)

  -- The ℕ₊-eliminator on Bits₊.
  elim-ℕ₊ : ∀{ℓ} → (T : Bits₊ → Type{ℓ}) → T(Values.𝟏₊) → ((i : Bits₊) → T(i) → T(𝐒(i))) → ((n : Bits₊) → T(n))
  elim-ℕ₊ T base step ∅       = base
  elim-ℕ₊ T base step (𝑇 ⊰ n) = elim-ℕ₊(T ∘ (𝑇 ⊰_))
    (step (𝐹 ⊰ ∅) (step ∅ base))
    (\i ti → step(𝐹 ⊰ (𝐒(i))) (step(𝑇 ⊰ i) ti))
    n
  elim-ℕ₊ T base step (𝐹 ⊰ n) = elim-ℕ₊(T ∘ (𝐹 ⊰_))
    (step ∅ base)
    (\i ti → step (𝑇 ⊰ i) (step(𝐹 ⊰ i) ti))
    n

  module _ where
    open import Data.Boolean.Numeral using (Bool-to-ℕ)
    open import Numeral.Natural as ℕ using (ℕ)
    import      Numeral.Natural.Oper as ℕ

    -- Converts a value of Bits₊ to a number by adding the first digit and multiplying the rest with the radix.
    toℕ : Bits₊ → ℕ
    toℕ ∅       = ℕ.𝟏
    toℕ (b ⊰ l) = ((toℕ l) ℕ.⋅ 2) ℕ.+ Bool-to-ℕ(b)

    import      Data.Option.Functions as Option
    open import Logic.Propositional
    open import Numeral.Natural.Oper.Divisibility
    open import Numeral.Natural.Oper.FlooredDivision
    open import Numeral.Natural.Oper.FlooredDivision.Proofs.Decidable
    open import Numeral.Natural.Relation

    -- Converts a number to its bit representation.
    -- This is done by checking divisibility for the extraction of the next bit and using recursion on the rest by dividing the value by 2.
    -- Note: This is the inverse of toℕ.
    -- Termination: (n ⌊/⌋ 2 < n) is true for all (n > 0).
    -- Alternative implementation (using well-founded recursion):
    --   open import Numeral.Natural.Inductions
    --   open import Numeral.Natural.Oper.FlooredDivision.Proofs
    --   open import Numeral.Natural.Relation.Order
    --   open import Structure.Relator.Ordering
    --
    --   from-ℕ-rec : (x : ℕ) → ((prev : ℕ) ⦃ _ : prev < x ⦄ → .⦃ pos : Positive(prev) ⦄ → Bits₊) → .⦃ pos : Positive(x) ⦄ → Bits₊
    --   from-ℕ-rec ℕ.𝟏            _    = ∅
    --   from-ℕ-rec n@(ℕ.𝐒(ℕ.𝐒 _)) prev = (2 ∤? n) ⊰ (prev(n ⌊/⌋ 2) ⦃ [⌊/⌋]-ltₗ {n}{2} ⦄ ⦃ [⌊/⌋]-positive-[≥?] {n}{2} ⦄)
    --   from-ℕ' : (n : ℕ) .⦃ pos : Positive(n) ⦄ → Bits₊
    --   from-ℕ' = Strict.Properties.wellfounded-recursion(_<_) from-ℕ-rec
    {-# TERMINATING #-}
    fromℕ : (n : ℕ) → .⦃ pos : Positive(n) ⦄ → Bits₊
    fromℕ ℕ.𝟏            = ∅
    fromℕ n@(ℕ.𝐒(ℕ.𝐒 _)) = (2 ∤? n) ⊰ fromℕ(n ⌊/⌋ 2) ⦃ [⌊/⌋]-positive-[≥?] {n}{2} ⦄

    open import Numeral.Natural.Oper.Proofs.Iteration
    open import Relator.Equals
    open import Relator.Equals.Proofs.Equiv
    open import Structure.Operator
    open import Syntax.Transitivity

    toℕ-preserve-𝐒 : ∀{n} → (toℕ(𝐒(n)) ≡ ℕ.𝐒(toℕ(n)))
    toℕ-preserve-𝐒 {∅}      = [≡]-intro
    toℕ-preserve-𝐒 {𝐹 ⊰ bs} = [≡]-intro
    toℕ-preserve-𝐒 {𝑇 ⊰ bs} =
      toℕ(𝐒(𝑇 ⊰ bs))          🝖[ _≡_ ]-[]
      toℕ(𝐒(bs)) ℕ.⋅ 2        🝖[ _≡_ ]-[ congruence₂-₁(ℕ._⋅_)(2) (toℕ-preserve-𝐒 {bs}) ]
      ℕ.𝐒(toℕ bs) ℕ.⋅ 2       🝖[ _≡_ ]-[ [⋅]-stepₗ-iterateᵣ-𝐒 {toℕ(bs)}{2} ]
      ℕ.𝐒(ℕ.𝐒(toℕ(bs) ℕ.⋅ 2)) 🝖[ _≡_ ]-[]
      ℕ.𝐒(toℕ(𝑇 ⊰ bs))        🝖-end

    {- TODO
    toℕ-positive : ∀{n} → Positive(toℕ(n))

    -- let bs = fromℕ(n) in P((n ℕ.⋅ 2) ℕ.+ Bool-to-ℕ(b))
    fromℕ-intro : ∀{ℓ} → (P : (n : ℕ) → .⦃ pos : Positive(n) ⦄ → Bits₊ → Type{ℓ})
                → P ℕ.𝟏 ∅
                → (∀{n} .⦃ pos : Positive(n) ⦄ {b} → P(n ⌊/⌋ 2) ⦃ {!!} ⦄ (fromℕ(n ⌊/⌋ 2) ⦃ {!!} ⦄) → P n (b ⊰ (fromℕ(n ⌊/⌋ 2) ⦃ {!!} ⦄)))
                → ∀{n} .⦃ pos : Positive(n) ⦄ → P n (fromℕ(n))
    fromℕ-intro P base step {ℕ.𝟏}          = base
    fromℕ-intro P base step n@{ℕ.𝐒(ℕ.𝐒 _)} = step{n} {2 ∤? n} (fromℕ-intro P base step {n ⌊/⌋ 2} ⦃ {!!} ⦄)

    open import Logic.Propositional.Equiv
    open import Structure.Relator
    open import Relator.Equals.Proofs.Equiv
    fromℕ-intro' : ∀{ℓ} → (P : (n : ℕ) → .⦃ pos : Positive(n) ⦄ → Bits₊ → Type{ℓ})
                → P ℕ.𝟏 ∅
                → (∀{n} .⦃ pos : Positive(n) ⦄ {b} → P(n) ⦃ {!!} ⦄ (fromℕ(n)) → P ((n ℕ.⋅ 2) ℕ.+ Bool-to-ℕ(b)) ⦃ {!!} ⦄ (b ⊰ fromℕ(n)))
                → ∀{n} .⦃ pos : Positive(n) ⦄ → P n (fromℕ(n))
    -- fromℕ-intro' P base step {n} = fromℕ-intro P base (\{n}{b} prev → {!step{n ⌊/⌋ 2} ⦃ ? ⦄ {b} prev!} ) {n}
    fromℕ-intro' P base step {ℕ.𝟏}          = base
    fromℕ-intro' P base step n@{ℕ.𝐒(ℕ.𝐒 _)} = {!step {n ⌊/⌋ 2} ⦃ ? ⦄ {2 ∤? n} (fromℕ-intro' P base step {n ⌊/⌋ 2} ⦃ ? ⦄)!}
    -- {!substitute₁ₗ(\e → P e ⦃ ? ⦄ (fromℕ(e))) ? (step{n ⌊/⌋ 2} ⦃ ? ⦄ {2 ∤? n} ?)!}

    fromℕ-of-[⋅2] : ∀{n} ⦃ pos : Positive(n) ⦄ → (fromℕ(n ℕ.⋅ 2) ⦃ {!!} ⦄ ≡ 𝐹 ⊰ fromℕ(n))

    fromℕ-toℕ-inverse : ∀{n} → (fromℕ(toℕ(n)) ⦃ toℕ-positive{n} ⦄ ≡ n)
    fromℕ-toℕ-inverse {∅} = [≡]-intro
    fromℕ-toℕ-inverse {𝐹 ⊰ n} =
      fromℕ(toℕ(𝐹 ⊰ n)) ⦃ _ ⦄   🝖[ _≡_ ]-[]
      fromℕ(toℕ(n) ℕ.⋅ 2) ⦃ _ ⦄ 🝖[ _≡_ ]-[ fromℕ-of-[⋅2] {toℕ(n)} ⦃ toℕ-positive{n} ⦄ ]
      𝐹 ⊰ fromℕ(toℕ(n)) ⦃ _ ⦄   🝖[ _≡_ ]-[ congruence₂-₂(_⊰_)(𝐹) (fromℕ-toℕ-inverse{n}) ]
      𝐹 ⊰ n                     🝖-end
    fromℕ-toℕ-inverse {𝑇 ⊰ n} =
      fromℕ(toℕ(𝑇 ⊰ n)) ⦃ _ ⦄        🝖[ _≡_ ]-[]
      fromℕ(ℕ.𝐒(toℕ(n) ℕ.⋅ 2)) ⦃ _ ⦄ 🝖[ _≡_ ]-[]
      fromℕ((toℕ(n) ℕ.⋅ 2) ℕ.+ Bool-to-ℕ(𝑇)) ⦃ _ ⦄ 🝖[ _≡_ ]-[ {!!} ]
      𝑇 ⊰ fromℕ(toℕ(n)) ⦃ _ ⦄        🝖[ _≡_ ]-[ congruence₂-₂(_⊰_)(𝑇) (fromℕ-toℕ-inverse{n}) ]
      𝑇 ⊰ n                          🝖-end
  -}

  -- open Syntax
  -- test = {!toℕ(#1· 0 · 1 · 0)!}

module Bits where
  -- Successor function of `Bits`.
  𝐒 : Bits → Bits
  𝐒 None    = Values.𝟏
  𝐒(Some n) = Some(Bits₊.𝐒(n))

  -- The ℕ-eliminator on Bits.
  elim-ℕ : ∀{ℓ} → (T : Bits → Type{ℓ}) → T(Values.𝟎) → ((i : Bits) → T(i) → T(𝐒(i))) → ((n : Bits) → T(n))
  elim-ℕ T base step None     = base
  elim-ℕ T base step (Some n) = Bits₊.elim-ℕ₊(T ∘ Some) (step None base) (step ∘ Some) n

  -- _+_ : Bits → Bits → Bits

  module _ where
    open import Numeral.Natural as ℕ using (ℕ)

    -- Converts a value of Bits to a number.
    toℕ : Bits → ℕ
    toℕ None     = ℕ.𝟎
    toℕ (Some n) = Bits₊.toℕ n

    -- Alternative implementation:
    --   import      Data.Option.Functions as Option
    --   open import Numeral.Natural.Oper.Divisibility
    --   open import Numeral.Natural.Oper.FlooredDivision
    --
    --   {-# TERMINATING #-}
    --   fromℕ : ℕ → Bits
    --   fromℕ ℕ.𝟎       = None
    --   fromℕ n@(ℕ.𝐒 _) = Some(Option.partialMap ∅ ((2 ∤? n) ⊰_) (fromℕ(n ⌊/⌋ 2)))
    fromℕ : ℕ → Bits
    fromℕ ℕ.𝟎       = None
    fromℕ n@(ℕ.𝐒 _) = Some(Bits₊.fromℕ n)

    open import Relator.Equals

    toℕ-preserve-𝐒 : ∀{n} → (toℕ(𝐒(n)) ≡ ℕ.𝐒(toℕ(n)))
    toℕ-preserve-𝐒 {None}   = [≡]-intro
    toℕ-preserve-𝐒 {Some x} = Bits₊.toℕ-preserve-𝐒 {x}

  -- open Syntax
  -- test = {!!}
  -- toℕ(+ #1· 0 · 1 · 0)
  -- toℕ(fromℕ 1)
