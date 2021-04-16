module Numeral.FixedPositional where

{-
FixedPositional : ℕ → Type
FixedPositional(b) = List(𝕟(b))

open import Numeral.Natural.Oper

private variable b : ℕ

to-ℕ : FixedPositional(b) → ℕ
to-ℕ {_} ∅       = 𝟎
to-ℕ {b} (n ⊰ l) = 𝕟-to-ℕ (n) + (b ⋅ to-ℕ (l))

-}

{-
module Test2 where
  import      Lvl
  open import Data
  open import Data.Boolean hiding (elim)
  open import Data.Boolean.Stmt
  import      Data.Boolean.Operators
  open        Data.Boolean.Operators.Programming
  open import Numeral.Finite
  open import Numeral.Natural
  open import Functional
  open import Syntax.Number
  open import Type
  open import Type.Dependent

  private variable ℓ : Lvl.Level
  private variable z : Bool
  private variable b n : ℕ

  positive? : 𝕟(n) → Bool
  positive? 𝟎     = 𝐹
  positive? (𝐒 _) = 𝑇

  Positive : 𝕟(n) → Type
  Positive = IsTrue ∘ positive?

  data Positional(b : ℕ) : Type{Lvl.𝟎} where
    #   : (n : 𝕟(b)) → ⦃ Positive(n) ⦄ → Positional b
    _·_ : Positional b → 𝕟(b) → Positional b
  infixl 20 _·_

  test : Positional 10
  test = # 1 · 5 · 0 · 4 · 0 · 0

  open import Numeral.Natural.Oper

  to-ℕ : Positional b → ℕ
  to-ℕ     (# n)   = 𝕟-to-ℕ n
  to-ℕ {b} (l · n) = (b ⋅ (to-ℕ l)) + (to-ℕ (# n))

  open import Logic.Propositional
  -- open import Numeral.Natural.Decidable
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
  open import Type.Properties.Decidable
  open import Type.Properties.Decidable.Proofs

  from-ℕ-rec : (b : ℕ) → ⦃ b-size : IsTrue(b >? 1) ⦄ → (x : ℕ) → ((prev : ℕ) ⦃ _ : prev < x ⦄ → Positional(b)) → Positional(b)
  from-ℕ-rec b@(𝐒(𝐒 _)) 𝟎       _    = intro 𝐹 (# 𝟎)
  from-ℕ-rec b@(𝐒(𝐒 _)) n@(𝐒 _) prev with prev(n ⌊/⌋ b) ⦃ [⌊/⌋]-ltₗ {n}{b} ⦄
  ... | intro 𝑇 r = intro 𝑇 (r · (ℕ-to-𝕟 (n mod b) ⦃ [↔]-to-[→] decider-true (mod-maxᵣ{n}{b}) ⦄))
  ... | intro 𝐹 r = {!test2 r [≡]-intro!}
  from-ℕ : ⦃ b-size : IsTrue(b >? 1) ⦄ → ℕ → Positional(b)
  from-ℕ b@{𝐒(𝐒 _)} = Strict.Properties.wellfounded-recursion(_<_) (from-ℕ-rec b)
  {-from-ℕ {b = b@(𝐒(𝐒 _))} 𝟎 = intro 𝐹 (# 𝟎)
  from-ℕ {b = b@(𝐒(𝐒 _))} n@(𝐒 _) with [<][≥]-dichotomy {n}{b}
  ... | [∨]-introₗ lt = intro 𝑇 (# (ℕ-to-𝕟 n ⦃ [↔]-to-[→] decider-true lt ⦄))
  ... | [∨]-introᵣ ge with from-ℕ {b} (n ⌊/⌋ b)
  ... |   intro 𝑇 nb = intro 𝑇 (nb · ℕ-to-𝕟 (n mod b) ⦃ [↔]-to-[→] decider-true (mod-maxᵣ{n}{b}) ⦄)
  ... |   intro 𝐹 _  = intro 𝑇 {!!}-}
-}

module Test where
  open import Data.List
  open import Numeral.Finite
  open import Numeral.Natural
  open import Type
  open import Numeral.Natural.Oper

  private variable b : ℕ

  to-ℕ : ℕ → List(ℕ) → ℕ
  to-ℕ _ ∅       = 𝟎
  to-ℕ b (n ⊰ l) = n + (b ⋅ to-ℕ b l)

  module _ where
    open import Data
    open import Data.Boolean.Stmt
    open import Numeral.Natural.Inductions
    open import Numeral.Natural.Oper.Comparisons
    open import Numeral.Natural.Oper.FlooredDivision
    open import Numeral.Natural.Oper.FlooredDivision.Proofs
    open import Numeral.Natural.Oper.Modulo
    open import Numeral.Natural.Relation
    open import Numeral.Natural.Relation.Order
    open import Relator.Equals
    open import Structure.Relator.Ordering

    from-ℕ-rec : (b : ℕ) → ⦃ b-size : IsTrue(b >? 1) ⦄ → (x : ℕ) → ((prev : ℕ) ⦃ _ : prev < x ⦄ → List ℕ) → List ℕ
    from-ℕ-rec b@(𝐒(𝐒 _)) 𝟎       _    = ∅
    from-ℕ-rec b@(𝐒(𝐒 _)) n@(𝐒 _) prev = (n mod b) ⊰ prev(n ⌊/⌋ b) ⦃ [⌊/⌋]-ltₗ {n} {b} ⦄
    from-ℕ : (b : ℕ) → ⦃ b-size : IsTrue(b >? 1) ⦄ → ℕ → List(ℕ)
    from-ℕ b@(𝐒(𝐒 _)) = Strict.Properties.wellfounded-recursion(_<_) (from-ℕ-rec b)

    open import Numeral.Natural.Oper.DivMod.Proofs
    open import Numeral.Natural.Oper.Proofs
    open import Structure.Function
    open import Structure.Operator
    open import Structure.Operator.Properties
    open import Syntax.Transitivity
    open import Relator.Equals.Proofs.Equiv

    to-from-inverse : ∀{b} ⦃ b-size : IsTrue(b >? 1) ⦄ {n} → (to-ℕ b (from-ℕ b n) ≡ n)
    to-from-inverse {b@(𝐒(𝐒 bb))} {n} = Strict.Properties.wellfounded-recursion-intro(_<_) {rec = from-ℕ-rec b} {φ = \{n} expr → (to-ℕ b expr ≡ n)} p {n} where
      p : (y : ℕ) → _ → _ → (to-ℕ b (Strict.Properties.accessible-recursion(_<_) (from-ℕ-rec b) y) ≡ y)
      p 𝟎     _    _    = [≡]-intro
      p (𝐒 y) prev step =
        to-ℕ b (Strict.Properties.accessible-recursion(_<_) (from-ℕ-rec b) (𝐒 y)) 🝖[ _≡_ ]-[ congruence₁(to-ℕ b) (step {𝐒(y) ⌊/⌋ b} ⦃ [⌊/⌋]-ltₗ {𝐒 y}{b} ⦄) ]
        (𝐒(y) mod b) + (b ⋅ to-ℕ b (Strict.Properties.accessible-recursion(_<_) (from-ℕ-rec b) (𝐒(y) ⌊/⌋ b))) 🝖[ _≡_ ]-[ congruence₂ᵣ(_+_)(𝐒(y) mod b) (congruence₂ᵣ(_⋅_)(b) (prev{𝐒(y) ⌊/⌋ b} ⦃ [⌊/⌋]-ltₗ {𝐒 y}{b} ⦄)) ]
        (𝐒(y) mod b) + (b ⋅ (𝐒(y) ⌊/⌋ b)) 🝖[ _≡_ ]-[ commutativity(_+_) {𝐒(y) mod b}{b ⋅ (𝐒(y) ⌊/⌋ b)} ]
        (b ⋅ (𝐒(y) ⌊/⌋ b)) + (𝐒(y) mod b) 🝖[ _≡_ ]-[ [⌊/⌋][mod]-is-division-with-remainder-pred-commuted {𝐒 y}{b} ]
        𝐒(y) 🝖-end

  -- TODO: There are some requirements on l for this to hold. For example, it should not end with zeroes (actually start with because the representation is reversed from the usual one), it should not have numbers greater or equal to b
  {-from-to-inverse : ∀{b} ⦃ b-size : IsTrue(b >? 1) ⦄ {l} → (from-ℕ b (to-ℕ b l) ≡ l)
  from-to-inverse b@{𝐒(𝐒 _)} {l = ∅} = [≡]-intro
  from-to-inverse b@{𝐒(𝐒 _)} {l = x ⊰ l} = {!!}-}
  {-Strict.Properties.wellfounded-recursion-intro(_<_) {rec = from-ℕ-rec b} {φ = \{n} expr → (expr ≡ from-ℕ b n)} p {x + (b ⋅ to-ℕ b l)} where
    p : (y : ℕ) → _ → _ → (Strict.Properties.accessible-recursion(_<_) (from-ℕ-rec b) y ≡ from-ℕ b y)
    p 𝟎 prev step = {!!}
    p (𝐒 y) prev step = {!!}-}

{-
module _ where
  open import Functional
  open import Function.Iteration using (repeatᵣ)
  open import Numeral.Natural.Induction
  open import Relator.Equals
  open import Relator.Equals.Proofs
  open import Syntax.Function
  open import Syntax.Transitivity

  {- TODO: Attempt to prove `∀a∀b. aᵇ = 1 + ((a−1) ⋅ ∑(0‥b) (i ↦ aⁱ))` inductively. An intuitive example of this is: `10³ = 1000 = 1+999 = 1+(9⋅111) = 1+(9⋅(1+10+100)) = 1+((10−1)⋅(10⁰+10¹+10²))`. This can also be proved by using the binomial theorem?
  powerSum : ℕ → ℕ → ℕ
  powerSum a 0         = 0
  powerSum a 1         = 1
  powerSum a (𝐒(𝐒(b))) = (powerSum a (𝐒(b))) + (a ⋅ (powerSum a (𝐒(b))))

  exponentiation-is-sum-of-parts : ∀{a b} → (𝐒(a) ^ b ≡ 𝐒(a ⋅ (powerSum (𝐒(a)) b)))
  exponentiation-is-sum-of-parts {a} {0}       = [≡]-intro
  exponentiation-is-sum-of-parts {a} {1}       = [≡]-intro
  exponentiation-is-sum-of-parts {a} {𝐒(b@(𝐒(_)))} =
    𝐒(a) ^ 𝐒(b)                     🝖[ _≡_ ]-[]
    𝐒(a) ⋅ (𝐒(a) ^ b)               🝖[ _≡_ ]-[ {!!} ]
    (𝐒(a) ^ b) + (𝐒(a) ⋅ (a ⋅ (powerSum (𝐒(a)) b)))                   🝖[ _≡_ ]-[ {!!} ]
    (𝐒(a) ^ b) + (a ⋅ (𝐒(a) ⋅ (powerSum (𝐒(a)) b)))                   🝖[ _≡_ ]-[ {!!} ]
    𝐒(a ⋅ (powerSum (𝐒(a)) b)) + (a ⋅ (𝐒(a) ⋅ (powerSum (𝐒(a)) b)))   🝖[ _≡_ ]-[ {!!} ]
    𝐒((a ⋅ (powerSum (𝐒(a)) b)) + (a ⋅ (𝐒(a) ⋅ (powerSum (𝐒(a)) b)))) 🝖[ _≡_ ]-[ {!!} ]
    𝐒(a ⋅ ((powerSum (𝐒(a)) b) + (𝐒(a) ⋅ (powerSum (𝐒(a)) b))))       🝖[ _≡_ ]-[]
    𝐒(a ⋅ (powerSum (𝐒(a)) (𝐒(b))))                                   🝖-end
  -}

module _ where
  open import Data.List.Functions
  open import Numeral.Natural.Relation.Order
  open import Numeral.Natural.Relation.Order.Proofs
  open import Structure.Relator.Properties
  open import Syntax.Transitivity

  {-
  FixedPositional-maximum : ∀{n : FixedPositional(b)} → (to-ℕ (n) < b ^ length(n))
  FixedPositional-maximum {_}   {∅}     = reflexivity(_≤_)
  FixedPositional-maximum {𝐒 b} {n ⊰ l} =
    𝐒(𝕟-to-ℕ (n) + (𝐒(b) ⋅ to-ℕ (l)))                               🝖[ _≤_ ]-[ {!!} ]
    𝐒(𝕟-to-ℕ (n) + (𝐒(b) ⋅ (b ^ length(l))))                        🝖[ _≤_ ]-[ {!!} ]
    𝐒(𝕟-to-ℕ (n) + ((b ⋅ (b ^ length(l))) + (1 ⋅ (b ^ length(l))))) 🝖[ _≤_ ]-[ {!!} ]
    𝐒(𝕟-to-ℕ (n) + ((b ^ 𝐒(length(l))) + (b ^ length(l))))          🝖[ _≤_ ]-[ {!!} ]
    ?                                                               🝖[ _≤_ ]-[ {!!} 
    (b ⋅ (𝐒(b) ^ length(l))) + (𝐒(b) ^ length(l))                   🝖[ _≤_ ]-[ {!!} ]
    𝐒(b) ⋅ (𝐒(b) ^ length(l))                                       🝖-end
  -}
-}
