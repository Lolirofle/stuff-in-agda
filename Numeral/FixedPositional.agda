module Numeral.FixedPositional where

import      Lvl
open import Data using (<>)
open import Data.List
open import Data.Boolean hiding (elim)
open import Data.Boolean.Stmt
open import Numeral.Finite
open import Numeral.Natural
open import Functional
open import Syntax.Number
open import Type

private variable ℓ : Lvl.Level
private variable z : Bool
private variable b n : ℕ

-- A formalization of the fixed positional radix numeral system for the notation of numbers.
-- Each number is represented by a list of digits.
-- Digits are a finite set of ordered objects starting with zero (0), and a finite number of its successors.
-- Examples using radix 10 (b = 10):
--   ∅                               represents 0
--   # 0                             represents 0
--   # 0 · 0                         represents 0
--   # 2                             represents 2
--   # 1 · 3                         represents 13
--   # 5 · 0 · 4 · 0 · 0             represents 50400
--   # 0 · 5 · 0 · 4 · 0 · 0         represents 50400
--   # 0 · 0 · 0 · 5 · 0 · 4 · 0 · 0 represents 50400
--   # 5 · 0 · 4 · 0 · 0 · 0         represents 504000
-- Example using radix 2 (b = 2):
--   # 1 · 1             represents 3
--   # 0 · 1 · 0 · 1 · 1 represents 11
-- Note: The radix is also called base.
-- Note: This representation is in little endian: The deepest digit in the list is the most significant digit (greatest), and the first position of the list is the least significant digit. Note that the (_·_) operator is a reversed list cons operator, so it constructs a list from right to left when written without parenthesis.
Positional = List ∘ 𝕟
pattern # n = n ⊰ ∅
pattern _·_ a b = b ⊰ a
infixl 100 _·_

private variable x y : Positional(b)
private variable d : 𝕟(n)

-- Two positionals are equal when the sequence of digits in the lists are the same.
-- But also, when there are zeroes at the most significant positions, they should be skipped.
-- Examples:
--   # 4 · 5         ≡ₚₒₛ # 4 · 5
--   # 0 · 0 · 4 · 5 ≡ₚₒₛ # 4 · 5
--   # 4 · 5         ≡ₚₒₛ # 0 · 0 · 4 · 5
--   # 0 · 0 · 4 · 5 ≡ₚₒₛ # 0 · 4 · 5
data _≡ₚₒₛ_ : Positional b → Positional b → Type{Lvl.𝟎} where
  empty : (_≡ₚₒₛ_ {b} ∅ ∅)
  skipₗ : (x ≡ₚₒₛ ∅) → (x · 𝟎 ≡ₚₒₛ ∅)
  skipᵣ : (∅ ≡ₚₒₛ y) → (∅ ≡ₚₒₛ y · 𝟎)
  step  : (x ≡ₚₒₛ y) → (x · d ≡ₚₒₛ y · d)

module _ where
  open import Numeral.Natural.Oper

  -- Converts a positional to a number by adding the first digit and multiplying the rest with the radix.
  -- Examples in radix 10 (b = 10):
  --   to-ℕ (# 1 · 2 · 3) = 10 ⋅ (10 ⋅ (10 ⋅ 0 + 1) + 2) + 3 = ((0 + 100) + 20) + 3 = 100 + 20 + 3 = 123
  --   to-ℕ (# a · b · c) = 10 ⋅ (10 ⋅ (10 ⋅ 0 + a) + b) + c = (10² ⋅ a) + (10¹ ⋅ b) + c = (10² ⋅ a) + (10¹ ⋅ b) + (10⁰ ⋅ c)
  to-ℕ : Positional b → ℕ
  to-ℕ     ∅       = 𝟎
  to-ℕ {b} (l · n) = (b ⋅ (to-ℕ l)) + (toℕ n)

  import      Data.List.Functions as List
  open import Logic.Propositional
  open import Numeral.Finite.Proofs
  open import Numeral.Natural.Inductions
  open import Numeral.Natural.Oper.Comparisons
  open import Numeral.Natural.Oper.FlooredDivision
  open import Numeral.Natural.Oper.FlooredDivision.Proofs
  open import Numeral.Natural.Oper.Modulo
  open import Numeral.Natural.Oper.Modulo.Proofs
  open import Numeral.Natural.Relation.Order
  open import Numeral.Natural.Relation.Order.Decidable
  open import Numeral.Natural.Relation.Order.Proofs
  open import Structure.Relator.Ordering
  import      Structure.Relator.Names as Names
  open import Structure.Relator.Equivalence
  open import Structure.Relator.Properties
  open import Syntax.Transitivity
  open import Type.Properties.Decidable
  open import Type.Properties.Decidable.Proofs

  -- Converts a number to its positional representation in the specified radix.
  -- This is done by extracting the next digit using modulo of the radix and then dividing the rest.
  -- This is the inverse of to-ℕ.
  from-ℕ-rec : ⦃ b-size : IsTrue(b >? 1) ⦄ → (x : ℕ) → ((prev : ℕ) ⦃ _ : prev < x ⦄ → Positional(b)) → Positional(b)
  from-ℕ-rec b@{𝐒(𝐒 _)} 𝟎       _    = ∅
  from-ℕ-rec b@{𝐒(𝐒 _)} n@(𝐒 _) prev = (prev(n ⌊/⌋ b) ⦃ [⌊/⌋]-ltₗ {n}{b} ⦄) · (fromℕ (n mod b) ⦃ [↔]-to-[→] decider-true (mod-maxᵣ{n}{b}) ⦄)
  from-ℕ : ℕ → Positional(b)
  from-ℕ {0}        = const ∅
  from-ℕ {1}        = List.repeat 𝟎
  from-ℕ b@{𝐒(𝐒 _)} = Strict.Properties.wellfounded-recursion(_<_) from-ℕ-rec

  instance
    [≡ₚₒₛ]-reflexivity : Reflexivity(_≡ₚₒₛ_ {b})
    [≡ₚₒₛ]-reflexivity = intro p where
      p : Names.Reflexivity(_≡ₚₒₛ_ {b})
      p {x = ∅}     = empty
      p {x = _ ⊰ _} = _≡ₚₒₛ_.step p

  instance
    [≡ₚₒₛ]-symmetry : Symmetry(_≡ₚₒₛ_ {b})
    [≡ₚₒₛ]-symmetry = intro p where
      p : Names.Symmetry(_≡ₚₒₛ_ {b})
      p empty            = empty
      p (skipₗ eq)       = skipᵣ (p eq)
      p (skipᵣ eq)       = skipₗ (p eq)
      p (_≡ₚₒₛ_.step eq) = _≡ₚₒₛ_.step (p eq)

  instance
    [≡ₚₒₛ]-transitivity : Transitivity(_≡ₚₒₛ_ {b})
    [≡ₚₒₛ]-transitivity = intro p where
      p : Names.Transitivity(_≡ₚₒₛ_ {b})
      p empty           empty           = empty
      p empty           (skipᵣ b)       = skipᵣ b
      p (skipₗ a)       empty           = skipₗ a
      p (skipₗ a)       (skipᵣ b)       = _≡ₚₒₛ_.step (p a b)
      p (skipᵣ a)       (skipₗ b)       = p a b
      p (skipᵣ a)       (_≡ₚₒₛ_.step b) = skipᵣ (p a b)
      p (_≡ₚₒₛ_.step a) (skipₗ b)       = skipₗ (p a b)
      p (_≡ₚₒₛ_.step a) (_≡ₚₒₛ_.step b) = _≡ₚₒₛ_.step (p a b)

  instance
    [≡ₚₒₛ]-equivalence : Equivalence(_≡ₚₒₛ_ {b})
    [≡ₚₒₛ]-equivalence = intro

  open import Structure.Setoid using (Equiv ; intro)

  Positional-equiv : Equiv(Positional(b))
  Positional-equiv {b} = intro _ ⦃ [≡ₚₒₛ]-equivalence {b} ⦄

  open import Functional.Instance
  open import Numeral.Natural.Relation.Proofs
  open import Structure.Function
  open import Structure.Operator
  open import Relator.Equals
  open import Relator.Equals.Proofs

  from-ℕ-digit : ⦃ b-size : IsTrue(b >? 1) ⦄ → ⦃ _ : IsTrue(n <? b) ⦄ → (from-ℕ {b} n ≡ₚₒₛ fromℕ n ⊰ ∅)
  from-ℕ-digit b@{𝐒(𝐒 bb)} {n} = Strict.Properties.wellfounded-recursion-intro(_<_) {rec = from-ℕ-rec} {φ = \{n} expr → ⦃ _ : IsTrue(n <? b) ⦄ → (expr ≡ₚₒₛ (fromℕ n ⊰ ∅))} p {n} where
    p : (y : ℕ) → _ → _ → ⦃ _ : IsTrue(y <? b) ⦄ → (from-ℕ y ≡ₚₒₛ (fromℕ y ⊰ ∅))
    p 𝟎 prev eq = skipᵣ empty
    p (𝐒 y) prev eq ⦃ ord ⦄ =
      from-ℕ (𝐒(y))                                                         🝖[ _≡ₚₒₛ_ ]-[ sub₂(_≡_)(_≡ₚₒₛ_) eq ]
      from-ℕ (𝐒(y) ⌊/⌋ b) · fromℕ (𝐒(y) mod b) ⦃ yb-ord? ⦄                 🝖[ _≡ₚₒₛ_ ]-[ _≡ₚₒₛ_.step (prev ⦃ [⌊/⌋]-ltₗ{𝐒 y}{b}  ⦄ ⦃ div-ord ⦄) ]
      ∅ · fromℕ (𝐒(y) ⌊/⌋ b) ⦃ div-ord ⦄ · fromℕ (𝐒(y) mod b) ⦃ yb-ord? ⦄ 🝖[ _≡ₚₒₛ_ ]-[ sub₂(_≡_)(_≡ₚₒₛ_) (congruence₂-₂(_·_)(∅ · fromℕ (𝐒(y) ⌊/⌋ b) ⦃ div-ord ⦄) (congruence-fromℕ {x = 𝐒(y) mod b} ⦃ yb-ord? ⦄ {y = 𝐒(y)} ⦃ ord ⦄ (mod-lesser-than-modulus {𝐒 y}{b} yb-ord))) ]
      ∅ · fromℕ (𝐒(y) ⌊/⌋ b) ⦃ div-ord ⦄ · fromℕ (𝐒(y))                   🝖[ _≡ₚₒₛ_ ]-[ _≡ₚₒₛ_.step (sub₂(_≡_)(_≡ₚₒₛ_) (congruence₂-₂(_·_)(_) (congruence-fromℕ ⦃ infer ⦄ ⦃ div-ord ⦄ ([⌊/⌋]-zero {𝐒 y}{b} yb-ord2)))) ]
      ∅ · 𝟎 · fromℕ (𝐒(y))                                                 🝖[ _≡ₚₒₛ_ ]-[ _≡ₚₒₛ_.step (skipₗ empty) ]
      ∅ · fromℕ (𝐒(y))                                                     🝖-end
      where
        yb-ord? = [↔]-to-[→] decider-true (mod-maxᵣ {𝐒(y)}{b} ⦃ infer ⦄)
        yb-ord = [↔]-to-[←] (decider-true ⦃ [<]-decider ⦄) ord
        yb-ord2 = [↔]-to-[←] (decider-true ⦃ [<]-decider ⦄) ord
        div-ord = [↔]-to-[→] (decider-true ⦃ [<]-decider ⦄) (subtransitivityₗ(_<_)(_≤_) ([⌊/⌋]-leₗ {b = b}) yb-ord2)

  from-ℕ-step : ⦃ b-size : IsTrue(b >? 1) ⦄
              → let pos = [↔]-to-[←] Positive-greater-than-zero ([≤]-predecessor ([↔]-to-[←] (decider-true ⦃ [<]-decider {1}{b} ⦄) b-size))
                in (from-ℕ {b} n ≡ₚₒₛ (from-ℕ {b} ((n ⌊/⌋ b) ⦃ pos ⦄)) · (fromℕ ((n mod b) ⦃ pos ⦄) ⦃ [↔]-to-[→] decider-true (mod-maxᵣ{n}{b} ⦃ pos ⦄) ⦄))
  from-ℕ-step b@{𝐒(𝐒 bb)} {n} = Strict.Properties.wellfounded-recursion-intro(_<_) {rec = from-ℕ-rec} {φ = \{n} expr → (expr ≡ₚₒₛ from-ℕ {b} (n ⌊/⌋ b) · (fromℕ (n mod b) ⦃ ord n ⦄))} p {n} where
    ord = \n → [↔]-to-[→] decider-true (mod-maxᵣ{n}{b})
    p : (y : ℕ) → _ → _ → Strict.Properties.accessible-recursion(_<_) from-ℕ-rec y ≡ₚₒₛ from-ℕ (y ⌊/⌋ b) · fromℕ (y mod b) ⦃ ord y ⦄
    p 𝟎     prev eq = skipᵣ empty
    p (𝐒 y) prev eq = (sub₂(_≡_)(_≡ₚₒₛ_) eq)

  open import Numeral.Natural.Oper.FlooredDivision.Proofs.Compatibility
  open import Numeral.Natural.Oper.FlooredDivision.Proofs.Inverse
  open import Numeral.Natural.Oper.Proofs
  open import Numeral.Natural.Relation.Divisibility.Proofs
  open import Structure.Operator.Properties
  from-ℕ-step-invs : ⦃ b-size : IsTrue(b >? 1) ⦄ → (from-ℕ {b} ((b ⋅ n) + (toℕ d)) ≡ₚₒₛ (from-ℕ {b} n) · d)
  from-ℕ-step-invs b@{𝐒(𝐒 bb)} {n}{d} =
    from-ℕ (b ⋅ n + toℕ d)                                                     🝖[ _≡ₚₒₛ_ ]-[ from-ℕ-step {n = b ⋅ n + toℕ d} ]
    from-ℕ ((b ⋅ n + toℕ d) ⌊/⌋ b) · (fromℕ ((b ⋅ n + toℕ d) mod b) ⦃ _ ⦄) 🝖[ _≡ₚₒₛ_ ]-[ sub₂(_≡_)(_≡ₚₒₛ_) (congruence₂(_·_) (congruence₁(from-ℕ) r) (congruence-fromℕ ⦃ infer ⦄ ⦃ ord1 ⦄ ⦃ ord2 ⦄ q 🝖 ℕ-𝕟-inverse)) ]
    from-ℕ n · d                                                                  🝖-end where
      ord1 = [↔]-to-[→] decider-true (mod-maxᵣ{(b ⋅ n) + (toℕ d)}{b})
      ord2 = [↔]-to-[→] decider-true (toℕ-bounded {b}{d})
      q =
        ((b ⋅ n) + toℕ d) mod b 🝖[ _≡_ ]-[ congruence₁(_mod b) (commutativity(_+_) {b ⋅ n}{toℕ d}) ]
        (toℕ d + (b ⋅ n)) mod b 🝖[ _≡_ ]-[ mod-of-modulus-sum-multiple {toℕ d}{b}{n} ]
        (toℕ d) mod b           🝖[ _≡_ ]-[ mod-lesser-than-modulus ([≤]-without-[𝐒] toℕ-bounded) ]
        toℕ d                   🝖-end
      r =
        (b ⋅ n + toℕ d) ⌊/⌋ b             🝖[ _≡_ ]-[ [⌊/⌋][+]-distributivityᵣ {b ⋅ n}{toℕ d}{b} ([∨]-introₗ (DivN n)) ]
        ((b ⋅ n) ⌊/⌋ b) + ((toℕ d) ⌊/⌋ b) 🝖[ _≡_ ]-[ congruence₂(_+_) ([⌊/⌋][swap⋅]-inverseOperatorᵣ {b}{n}) ([⌊/⌋]-zero (toℕ-bounded {b}{d})) ]
        n + 𝟎                                🝖[ _≡_ ]-[]
        n                                    🝖-end

  open import Numeral.Natural.Oper.DivMod.Proofs
  open import Structure.Function.Domain
  import      Structure.Function.Names as Names

  instance
    from-to-inverse : ⦃ b-size : IsTrue(b >? 1) ⦄ → Inverseᵣ ⦃ Positional-equiv{b} ⦄ from-ℕ to-ℕ
    from-to-inverse b@{𝐒(𝐒 _)} = intro p where
      p : Names.Inverses ⦃ Positional-equiv{b} ⦄ from-ℕ to-ℕ
      p{x = ∅}     = empty
      p{x = x · n} = from-ℕ-step-invs{b}{to-ℕ x}{n} 🝖 _≡ₚₒₛ_.step (p{x = x})

  instance
    to-from-inverse : ⦃ b-size : IsTrue(b >? 1) ⦄ → Inverseᵣ(to-ℕ{b}) (from-ℕ{b})
    to-from-inverse {b@(𝐒(𝐒 bb))} = intro (\{n} → Strict.Properties.wellfounded-recursion-intro(_<_) {rec = from-ℕ-rec {b}} {φ = \{n} expr → (to-ℕ expr ≡ n)} p {n}) where
      p : (y : ℕ) → _ → _ → (to-ℕ {b} (from-ℕ {b} y) ≡ y)
      p 𝟎     _    _  = [≡]-intro
      p (𝐒 y) prev eq =
        to-ℕ {b} (from-ℕ (𝐒 y))                                                       🝖[ _≡_ ]-[ congruence₁(to-ℕ) eq ]
        to-ℕ {b} ((from-ℕ (𝐒(y) ⌊/⌋ b)) · (fromℕ (𝐒(y) mod b) ⦃ _ ⦄))                🝖[ _≡_ ]-[]
        (b ⋅ to-ℕ {b} (from-ℕ {b} (𝐒(y) ⌊/⌋ b))) + toℕ (fromℕ (𝐒(y) mod b) ⦃ _ ⦄) 🝖[ _≡_ ]-[ congruence₂(_+_) (congruence₂-₂(_⋅_)(b) (prev{𝐒(y) ⌊/⌋ b} ⦃ ord2 ⦄)) (𝕟-ℕ-inverse {b}{𝐒(y) mod b} ⦃ ord1 ⦄) ]
        (b ⋅ (𝐒(y) ⌊/⌋ b)) + (𝐒(y) mod b)                                             🝖[ _≡_ ]-[ [⌊/⌋][mod]-is-division-with-remainder-pred-commuted {𝐒 y}{b} ]
        𝐒(y)                                                                          🝖-end
        where
          ord1 = [↔]-to-[→] decider-true (mod-maxᵣ{𝐒(y)}{b})
          ord2 = [⌊/⌋]-ltₗ {𝐒 y}{b}

  instance
    to-ℕ-function : ⦃ b-size : IsTrue(b >? 1) ⦄ → Function ⦃ Positional-equiv ⦄ ⦃ [≡]-equiv ⦄ (to-ℕ {b})
    to-ℕ-function {b} = intro p where
      p : Names.Congruence₁ ⦃ Positional-equiv ⦄ ⦃ [≡]-equiv ⦄ (to-ℕ {b})
      p empty                          = reflexivity(_≡_)
      p (skipₗ xy) rewrite p xy        = reflexivity(_≡_)
      p (skipᵣ {y = ∅} xy)             = reflexivity(_≡_)
      p (skipᵣ {y = 𝟎 ⊰ y} (skipᵣ xy))
        rewrite symmetry(_≡_) (p xy)   = reflexivity(_≡_)
      p (_≡ₚₒₛ_.step xy)
        rewrite p xy = reflexivity(_≡_)

  open import Logic.Predicate
  open import Structure.Function.Domain.Proofs

  instance
    from-ℕ-bijective : ⦃ b-size : IsTrue(b >? 1) ⦄ → Bijective ⦃ [≡]-equiv ⦄ ⦃ Positional-equiv ⦄ (from-ℕ {b})
    from-ℕ-bijective = [↔]-to-[→] (invertible-when-bijective ⦃ _ ⦄ ⦃ _ ⦄) ([∃]-intro to-ℕ ⦃ [∧]-intro infer ([∧]-intro infer infer) ⦄)

  instance
    to-ℕ-bijective : ⦃ b-size : IsTrue(b >? 1) ⦄ → Bijective ⦃ Positional-equiv ⦄ ⦃ [≡]-equiv ⦄ (to-ℕ {b})
    to-ℕ-bijective = [↔]-to-[→] (invertible-when-bijective ⦃ _ ⦄ ⦃ _ ⦄) ([∃]-intro from-ℕ ⦃ [∧]-intro ([≡]-to-function ⦃ Positional-equiv ⦄) ([∧]-intro infer infer) ⦄)

  import      Data.Option.Functions as Option
  open import Function.Names
  open import Numeral.Natural.Relation.Order.Proofs

  -- TODO: Trying to define a bijection, but not really possible because not all functions
  PositionalSequence : List(𝕟(𝐒 b)) → (ℕ → 𝕟(𝐒 b))
  PositionalSequence l n = (List.index₀ n l) Option.or 𝟎

  sequencePositional : (f : ℕ → 𝕟(𝐒 b)) → ∃(N ↦ (f ∘ (_+ N) ⊜ const 𝟎)) → List(𝕟(𝐒 b))
  sequencePositional f ([∃]-intro 𝟎)           = ∅
  sequencePositional f ([∃]-intro (𝐒 N) ⦃ p ⦄) = f(𝟎) ⊰ sequencePositional (f ∘ 𝐒) ([∃]-intro N ⦃ \{n} → p{n} ⦄)
