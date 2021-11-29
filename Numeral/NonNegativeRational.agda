module Numeral.NonNegativeRational where

open import Data
import      Lvl
open import Syntax.Number
open import Type

module _ where
  open import Numeral.Natural as ℕ using (ℕ)
  open import Numeral.Natural.Relation as ℕ

  -- TODO: Maybe define this more generally so that the numerator could be ℤ also? Maybe by requiring that the denominator is a scalar in some kind of weak vector space with the numerator as vectors?
  record ℚ₊₀ : Type{Lvl.𝟎} where
    constructor _/ₙ_
    eta-equality
    field
      numerator   : ℕ
      denominator : ℕ
      ⦃ .positive ⦄ : ℕ.Positive(denominator)

  𝟎 : ℚ₊₀
  𝟎 = ℕ.𝟎 /ₙ ℕ.𝟏

  𝟏 : ℚ₊₀
  𝟏 = ℕ.𝟏 /ₙ ℕ.𝟏

  ⅟ₙ : (x : ℕ) .⦃ pos : Positive(x) ⦄ → ℚ₊₀
  ⅟ₙ x = ℕ.𝟏 /ₙ x

  ¼ = 1 /ₙ 4
  ½ = 1 /ₙ 2
  ¾ = 3 /ₙ 4
  ⅐ = 1 /ₙ 7
  ⅑ = 1 /ₙ 9
  ⅒ = 1 /ₙ 10
  ⅓ = 1 /ₙ 3
  ⅔ = 2 /ₙ 3
  ⅕ = 1 /ₙ 5
  ⅖ = 2 /ₙ 5
  ⅗ = 3 /ₙ 5
  ⅘ = 4 /ₙ 5
  ⅙ = 1 /ₙ 6
  ⅚ = 5 /ₙ 6
  ⅛ = 1 /ₙ 8
  ⅜ = 3 /ₙ 8
  ⅝ = 5 /ₙ 8
  ⅞ = 7 /ₙ 8

  fromℕ : ℕ → ℚ₊₀
  fromℕ(n) = n /ₙ ℕ.𝟏

  instance
    ℚ₊₀-InfiniteNumeral : InfiniteNumeral(ℚ₊₀)
    ℚ₊₀-InfiniteNumeral = InfiniteNumeral.intro(fromℕ)

module _ where
  open import Numeral.Natural
  import      Numeral.Natural.Oper as ℕ

  -- Cross-multiplied numbers of two rational numbers on an operator.
  -- x₁    x₂
  -- ―― ⤩ ――
  -- y₁    y₂
  crossMul : ∀{ℓ}{T : Type{ℓ}} → (ℕ → ℕ → T) → (ℚ₊₀ → ℚ₊₀ → T)
  crossMul(_▫_) (x₁ /ₙ y₁) (x₂ /ₙ y₂) = (x₁ ℕ.⋅ y₂) ▫ (x₂ ℕ.⋅ y₁)

  -- Cross-multiplied numbers of two rational numbers on an operator.
  -- x₁    x₂
  -- ―― ⤨ ――
  -- y₁    y₂
  crossMulAlt : ∀{ℓ}{T : Type{ℓ}} → (ℕ → ℕ → T) → (ℚ₊₀ → ℚ₊₀ → T)
  crossMulAlt(_▫_) (x₁ /ₙ y₁) (x₂ /ₙ y₂) = (x₁ ℕ.⋅ y₂) ▫ (y₁ ℕ.⋅ x₂)

  open import Logic.Propositional
  import      Numeral.Natural.Oper.Proofs as ℕ
  import      Numeral.Natural.Relation as ℕ
  open import Relator.Equals.Proofs.Equiv
  open import Structure.Operator.Proofs.Util
  open import Structure.Relator
  open import Structure.Relator.Properties
  open import Syntax.Implication
  private variable ℓ : Lvl.Level
  private variable _▫_ _△_  : ℕ → ℕ → Type{ℓ}

  crossMul-reflexivity : ⦃ Reflexivity(_▫_) ⦄ → Reflexivity(crossMul(_▫_))
  crossMul-reflexivity {_▫_ = _▫_} = intro(reflexivity(_▫_))

  crossMul-symmetry : ⦃ Symmetry(_▫_) ⦄ → Symmetry(crossMul(_▫_))
  crossMul-symmetry {_▫_ = _▫_} = intro(symmetry(_▫_))

  crossMul-transitivity : (∀{x y z} → ⦃ ℕ.Positive(z) ⦄ → (x ▫ y) ↔ ((x ℕ.⋅ z) ▫ (y ℕ.⋅ z)))
                          → ⦃ Transitivity(_▫_) ⦄ → Transitivity(crossMul(_▫_))
  Transitivity.proof (crossMul-transitivity {_▫_ = _▫_} p) {x₁ /ₙ y₁@(𝐒 _)} {x₂ /ₙ y₂@(𝐒 _)} {x₃ /ₙ y₃@(𝐒 _)} xy12 xy23 =
    • (xy12 ⇒
      (x₁ ℕ.⋅ y₂) ▫ (x₂ ℕ.⋅ y₁)                   ⇒-[ [↔]-to-[→] (p{z = y₃}) ]
      ((x₁ ℕ.⋅ y₂) ℕ.⋅ y₃) ▫ ((x₂ ℕ.⋅ y₁) ℕ.⋅ y₃) ⇒-end
    )
    • (xy23 ⇒
      (x₂ ℕ.⋅ y₃) ▫ (x₃ ℕ.⋅ y₂)                   ⇒-[ [↔]-to-[→] (p{z = y₁}) ]
      ((x₂ ℕ.⋅ y₃) ℕ.⋅ y₁) ▫ ((x₃ ℕ.⋅ y₂) ℕ.⋅ y₁) ⇒-[ substitute₂ₗ(_▫_) (One.commuteᵣ-assocₗ{a = x₂}{b = y₃}{c = y₁}) ]
      ((x₂ ℕ.⋅ y₁) ℕ.⋅ y₃) ▫ ((x₃ ℕ.⋅ y₂) ℕ.⋅ y₁) ⇒-end
    )
    ⇒₂-[ transitivity(_▫_) ]
    ((x₁ ℕ.⋅ y₂) ℕ.⋅ y₃) ▫ ((x₃ ℕ.⋅ y₂) ℕ.⋅ y₁) ⇒-[ substitute₂(_▫_) (One.commuteᵣ-assocₗ{a = x₁}{b = y₂}{c = y₃}) (One.commuteᵣ-assocₗ{a = x₃}{b = y₂}{c = y₁}) ]
    ((x₁ ℕ.⋅ y₃) ℕ.⋅ y₂) ▫ ((x₃ ℕ.⋅ y₁) ℕ.⋅ y₂) ⇒-[ [↔]-to-[←] (p{x₁ ℕ.⋅ y₃}{x₃ ℕ.⋅ y₁}{y₂}) ]
    (x₁ ℕ.⋅ y₃) ▫ (x₃ ℕ.⋅ y₁)                   ⇒-[]
    crossMul(_▫_) (x₁ /ₙ y₁) (x₃ /ₙ y₃)         ⇒-end

  crossMul-irreflexivity : ⦃ Irreflexivity(_▫_) ⦄ → Irreflexivity(crossMul(_▫_))
  crossMul-irreflexivity {_▫_ = _▫_} = intro(irreflexivity(_▫_))

  crossMul-asymmetry : ⦃ Asymmetry(_▫_) ⦄ → Asymmetry(crossMul(_▫_))
  crossMul-asymmetry {_▫_ = _▫_} = intro(asymmetry(_▫_))

  crossMul-antisymmetry : ⦃ Antisymmetry(_▫_)(_△_) ⦄ → Antisymmetry(crossMul(_▫_))(crossMul(_△_))
  crossMul-antisymmetry {_▫_ = _▫_} {_△_ = _△_} = intro(antisymmetry(_▫_)(_△_))

module _ where
  open import Functional
  open import Functional.Instance
  open import Numeral.Natural as ℕ using (ℕ)
  import      Numeral.Natural.Oper as ℕ
  import      Numeral.Natural.Oper.Proofs as ℕ
  import      Numeral.Natural.Relation as ℕ

  Positive : ℚ₊₀ → Type
  Positive = ℕ.Positive ∘ ℚ₊₀.numerator

  -- TODO: Consider using crossMul in the numerator instead. This would require all proofs to be fixed because the difference is that (y₁ ℕ.⋅ x₂) is swapped around.
  additiveOp : (ℕ → ℕ → ℕ) → (ℚ₊₀ → ℚ₊₀ → ℚ₊₀)
  additiveOp(_▫_) q₁@(x₁ /ₙ y₁) q₂@(x₂ /ₙ y₂) = (crossMulAlt(_▫_) q₁ q₂ /ₙ (y₁ ℕ.⋅ y₂)) ⦃ ℕ.[⋅]-positiveᵣ{y₁}{y₂} infer infer ⦄

  -- TODO: Some proofs of the properties of _+_ is able to be generalized to additiveOp
  _+_ : ℚ₊₀ → ℚ₊₀ → ℚ₊₀
  _+_ = additiveOp(ℕ._+_)

  _−₀_ : ℚ₊₀ → ℚ₊₀ → ℚ₊₀
  _−₀_ = additiveOp(ℕ._−₀_)

  _⋅_ : ℚ₊₀ → ℚ₊₀ → ℚ₊₀
  (x₁ /ₙ y₁) ⋅ (x₂ /ₙ y₂) = ((x₁ ℕ.⋅ x₂) /ₙ (y₁ ℕ.⋅ y₂)) ⦃ ℕ.[⋅]-positiveᵣ{y₁}{y₂} infer infer ⦄

  ⅟ : (x : ℚ₊₀) .⦃ pos : Positive(x) ⦄ → ℚ₊₀
  ⅟(x /ₙ y) = y /ₙ x

  _/_ : ℚ₊₀ → (y : ℚ₊₀) .⦃ pos : Positive(y) ⦄ → ℚ₊₀
  x / y = x ⋅ (⅟ y)

module _ where
  open import Data.Tuple
  open import Logic.Propositional
  open import Numeral.Natural
  import      Numeral.Natural.Oper as ℕ
  open import Numeral.Natural.Oper.CeiledDivision as ℕ
  open import Numeral.Natural.Oper.FlooredDivision as ℕ
  open import Numeral.Natural.Oper.Modulo as ℕ
  import      Numeral.Natural.Function.Coprimalize as ℕ
  import      Numeral.Natural.Function.GreatestCommonDivisor as ℕ

  -- Normalize the internal representation in the ℚ₊₀ type.
  -- Normalization in this context means making the numerator and denominator coprime by removing all common primes.
  normalize : ℚ₊₀ → ℚ₊₀
  normalize((x /ₙ y) ⦃ pos-y ⦄) =
    let (nx , ny) = ℕ.coprimalize(x , y)
    in (nx /ₙ ny) ⦃ [↔]-to-[→] ([∧]-elimᵣ ℕ.coprimalize-positive) pos-y ⦄

  -- Floor function to ℕ. Round toward 0.
  -- Examples:
  --   floor(20 /ₙ 10) = 2
  --   floor(21 /ₙ 10) = 2
  --   floor(25 /ₙ 10) = 2
  --   floor(29 /ₙ 10) = 2
  --   floor(30 /ₙ 10) = 3
  floor : ℚ₊₀ → ℕ
  floor(x /ₙ y) = x ⌊/⌋ y

  -- Ceiling function to ℕ. Round toward +∞.
  -- Examples:
  --   ceil(20 /ₙ 10) = 2
  --   ceil(21 /ₙ 10) = 3
  --   ceil(25 /ₙ 10) = 3
  --   ceil(29 /ₙ 10) = 3
  --   ceil(30 /ₙ 10) = 3
  ceil : ℚ₊₀ → ℕ
  ceil(x /ₙ y) = x ⌈/⌉ y

  -- Round function to ℕ. Round toward the nearest natural number, prefering +∞ in an ambiguous situation.
  -- Examples:
  --   round(20 /ₙ 10) = 2
  --   round(21 /ₙ 10) = 2
  --   round(25 /ₙ 10) = 3
  --   round(29 /ₙ 10) = 3
  --   round(30 /ₙ 10) = 3
  round : ℚ₊₀ → ℕ
  round(q) = floor(q + ½)

  -- Fractional part of 
  frac : ℚ₊₀ → ℚ₊₀
  frac(x /ₙ y) = (x mod y) /ₙ y

module _ where
  open import Functional
  open import Logic.Propositional
  open import Numeral.Natural
  import      Numeral.Natural.Oper as ℕ
  open import Numeral.Natural.Oper.Proofs.Multiplication
  import      Numeral.Natural.Relation.Order as ℕ
  open import Relator.Equals.Proofs.Equiv
  open import Structure.Operator
  open import Structure.Relator.Equivalence
  open import Structure.Setoid using (Equiv)
  open import Type.Identity

  _≤_ = crossMul(ℕ._≤_)
  _<_ = crossMul(ℕ._<_)

  open import Relator.Ordering
  open From-[≤][<] (_≤_)(_<_) public

  instance
    ℚ₊₀-equiv : Equiv(ℚ₊₀)
    Equiv._≡_ ℚ₊₀-equiv = crossMul(Id)
    Equivalence.reflexivity  (Equiv.equivalence ℚ₊₀-equiv) = crossMul-reflexivity
    Equivalence.symmetry     (Equiv.equivalence ℚ₊₀-equiv) = crossMul-symmetry
    Equivalence.transitivity (Equiv.equivalence ℚ₊₀-equiv) = crossMul-transitivity (\{x}{y}{z} → [↔]-intro ([⋅]-cancellationᵣ {z}{x}{y}) (congruence₂ₗ(ℕ._⋅_)(z)))

  open Equiv(ℚ₊₀-equiv) public
    using (_≡_ ; _≢_)
    {-renaming (
      reflexivity  to [≡]-reflexivity ;
      symmetry     to [≡]-symmetry ;
      transitivity to [≡]-transitivity
    )-}

module _ where
  open import Data.Tuple
  open import Logic.Predicate
  open import Logic.Propositional
  open import Numeral.Natural
  import      Numeral.Natural.Oper as ℕ
  import      Numeral.Natural.Oper.FlooredDivision as ℕ
  open import Numeral.Natural.Oper.FlooredDivision.Proofs
  open import Numeral.Natural.Oper.FlooredDivision.Proofs.Compatibility
  import      Numeral.Natural.Function.Coprimalize as ℕ
  import      Numeral.Natural.Function.GreatestCommonDivisor as ℕ
  open import Numeral.Natural.Function.GreatestCommonDivisor.Proofs
  import      Numeral.Natural.Relation as ℕ
  open import Structure.Operator
  open import Syntax.Transitivity
  open import Type.Identity
  open import Type.Identity.Proofs

  [/ₙ]-equality : ∀{x₁ x₂ y₁ y₂} ⦃ pos-x₂ : ℕ.Positive(x₂) ⦄ ⦃ pos-y₂ : ℕ.Positive(y₂) ⦄ → Id x₁ y₁ → Id x₂ y₂ → Id (x₁ /ₙ x₂) (y₁ /ₙ y₂)
  [/ₙ]-equality intro intro = intro

  normalize-identity : ∀{x} → (normalize x ≡ x)
  normalize-identity {x /ₙ y} = -- TODO: This is used in coprimalize-quotient-equality
    (x ℕ.⌊/⌋₀ (ℕ.gcd x y)) ℕ.⋅ y 🝖[ Id ]-[ [⌊/⌋₀][⋅]ₗ-compatibility {x}{y}{ℕ.gcd x y} (gcd-dividesₗ{x}{y}) ]-sym
    (x ℕ.⋅ y) ℕ.⌊/⌋₀ (ℕ.gcd x y) 🝖[ Id ]-[ [⌊/⌋₀][⋅]ᵣ-compatibility {x}{y}{ℕ.gcd x y} (gcd-dividesᵣ{x}{y}) ]
    x ℕ.⋅ (y ℕ.⌊/⌋₀ (ℕ.gcd x y)) 🝖-end

  import      Numeral.Natural.Relation.Divisibility as ℕ
  import      Numeral.Natural.Relation.Divisibility.Proofs as ℕ
  import      Numeral.Natural.Oper.FlooredDivision.Proofs.Inverse as ℕ
  ℚ-substitute-divides : ∀{x₁ x₂ y₁ y₂} ⦃ pos-x₂ : ℕ.Positive(x₂) ⦄ ⦃ pos-y₂ : ℕ.Positive(y₂) ⦄ → ((x₁ /ₙ x₂) ≡ (y₁ /ₙ y₂)) → (y₁ ℕ.∣ y₂) → (x₁ ℕ.∣ x₂)
  ℚ-substitute-divides {x₁}{x₂}{𝟎}{y₂} ⦃ _ ⦄ ⦃ pos-y₂ ⦄ _ div
    with intro ← ℕ.[0]-only-divides-[0] div
    with () ← pos-y₂
  ℚ-substitute-divides {x₁}{x₂}{y₁@(𝐒 _)}{y₂} eq div =
    let
      p =
        x₁ ℕ.⋅ (y₂ ℕ.⌊/⌋₀ y₁) 🝖[ Id ]-[ [⌊/⌋₀][⋅]ᵣ-compatibility {x₁}{y₂}{y₁} div ]-sym
        (x₁ ℕ.⋅ y₂) ℕ.⌊/⌋₀ y₁ 🝖[ Id ]-[ congruence₂ₗ(ℕ._⌊/⌋₀_)(y₁) eq ]
        (y₁ ℕ.⋅ x₂) ℕ.⌊/⌋₀ y₁ 🝖[ Id ]-[ ℕ.[⌊/⌋][swap⋅]-inverseOperatorᵣ {y₁}{x₂} ]
        x₂                    🝖-end
    in [↔]-to-[→] ℕ.divides-[⋅]-existence ([∃]-intro (y₂ ℕ.⌊/⌋₀ y₁) ⦃ p ⦄)
    where
      open import Numeral.Natural.Oper.Proofs
      open import Relator.Equals.Proofs.Equiv
      open import Structure.Operator.Properties

  -- test2 : ∀{x₁ x₂ y₁ y₂} ⦃ pos-x₂ : ℕ.Positive(x₂) ⦄ ⦃ pos-y₂ : ℕ.Positive(y₂) ⦄ → ((x₁ /ₙ x₂) ≡ (y₁ /ₙ y₂)) → ((x₁ ℕ.∣ y₁) ∨ (y₁ ℕ.∣ x₁))

  normalize-function : ∀{x y} → (x ≡ y) → (normalize x ≡ normalize y)
  normalize-function {x@(x₁ /ₙ x₂)}{y@(y₁ /ₙ y₂)} xy =
    Transitivity.proof [≡]-transitivity {normalize x}{x}{normalize y} (normalize-identity{x}) (
    Transitivity.proof [≡]-transitivity {x}{y}{normalize y} xy (symmetry(_≡_) {normalize y}{y} (normalize-identity{y})))
    {-
    normalize x 🝖[ _≡_ ]-[ normalize-identity{x} ]
    x           🝖[ _≡_ ]-[ xy ]
    y           🝖[ _≡_ ]-[ normalize-identity{y} ]-sym
    normalize y 🝖[ _≡_ ]-end
    -}
    where
      open import Structure.Relator.Properties
      open import Structure.Setoid using (Equiv)
      open Equiv(ℚ₊₀-equiv)
        using ()
        renaming (
          reflexivity  to [≡]-reflexivity ;
          symmetry     to [≡]-symmetry ;
          transitivity to [≡]-transitivity
        )

  open import Numeral.Natural.Coprime
  -- When the pairs (x₁,x₂) and (y₁,y₂) both are coprime and have the same ratio, they are equal.
  -- In other words, if (x₁/x₂ = y₁/y₂) when viewing the ratios as rational numbers, and they are both in their reduced forms, then the two numerators and the two denominators are equal.
  Coprime-unique-quotient : ∀{x₁ x₂ y₁ y₂} → Coprime x₁ x₂ → Coprime y₁ y₂ → Id(x₁ ℕ.⋅ y₂) (y₁ ℕ.⋅ x₂) → (Id x₁ y₁) ∧ (Id x₂ y₂)
  Coprime-unique-quotient {x₁}{x₂}{y₁}{y₂} coprim-x coprim-y eq =
    let
      proof : ∀{a b c d} → Coprime a b → Id(a ℕ.⋅ c) (b ℕ.⋅ d) → (a ∣ d)
      proof {a}{b}{c}{d} coprim eq =
        • (eq ⇒
          Id (a ℕ.⋅ c) (b ℕ.⋅ d)        ⇒-[ p ↦ [∃]-intro c ⦃ p ⦄ ]
          ∃(n ↦ Id(a ℕ.⋅ n) (b ℕ.⋅ d))  ⇒-[ [↔]-to-[→] divides-[⋅]-existence ]
          (a ∣ (b ℕ.⋅ d))               ⇒-end
        )
        • Coprime a b :-[ coprim ]
        ⇒₂-[ coprime-divides-of-[⋅] ]
        (a ∣ d) ⇒-end
    in
      • (
        • (x₁ ∣ y₁) :-[ proof{c = y₂} coprim-x (eq 🝖 commutativity(ℕ._⋅_) {y₁}{x₂}) ]
        • (y₁ ∣ x₁) :-[ proof{c = x₂} coprim-y (symmetry(Id) eq 🝖 commutativity(ℕ._⋅_) {x₁}{y₂}) ]
        ⇒₂-[ antisymmetry(_∣_)(Id) ]
        Id x₁ y₁ ⇒-end
      )
      • (
        • (x₂ ∣ y₂) :-[ proof{c = y₁} (symmetry(Coprime) coprim-x) (commutativity(ℕ._⋅_) {x₂}{y₁} 🝖 symmetry(Id) eq) ]
        • (y₂ ∣ x₂) :-[ proof{c = x₁} (symmetry(Coprime) coprim-y) (commutativity(ℕ._⋅_) {y₂}{x₁} 🝖 eq) ]
        ⇒₂-[ antisymmetry(_∣_)(Id) ]
        Id x₂ y₂ ⇒-end
      )
      ⇒₂-[ [∧]-intro ]
      (Id x₁ y₁) ∧ (Id x₂ y₂) ⇒-end
    where
      open import Numeral.Natural.Coprime.Proofs
      open import Numeral.Natural.Oper.Proofs
      open import Numeral.Natural.Relation.Divisibility
      open import Numeral.Natural.Relation.Divisibility.Proofs
      open import Numeral.Natural.Relation.Divisibility.Proofs.Product
      open import Relator.Equals.Proofs.Equiv
      open import Structure.Operator.Properties
      open import Structure.Relator.Properties
      open import Syntax.Function
      open import Syntax.Implication
      open import Syntax.Transitivity
      open import Syntax.Type

  open import Functional
  open import Numeral.Natural.Function.Coprimalize
  normalize-normal : ∀{x y} → (x ≡ y) → Id (normalize x) (normalize y)
  normalize-normal {x@((x₁ /ₙ x₂) ⦃ ipos-x₂ ⦄)}{y@((y₁ /ₙ y₂) ⦃ ipos-y₂ ⦄)} xy =
    uncurry ([/ₙ]-equality ⦃ pos-nx ⦄ ⦃ pos-ny ⦄) (Coprime-unique-quotient
      (coprimalize-is-coprime ([∨]-introᵣ pos-x₂))
      (coprimalize-is-coprime ([∨]-introᵣ pos-y₂))
      (normalize-function{x}{y} xy)
    )
    where
      open import Type.Properties.Decidable.Proofs
      open import Lang.Irrelevance.Convertable
      open import Numeral.Natural.Relation.Divisibility.Proofs.Product
      pos-x₂ = convert(ℕ.Positive(x₂)) ⦃ decider-convertable ⦄ ipos-x₂
      pos-y₂ = convert(ℕ.Positive(y₂)) ⦃ decider-convertable ⦄ ipos-y₂
      pos-nx = [↔]-to-[→] ([∧]-elimᵣ (coprimalize-positive)) pos-x₂
      pos-ny = [↔]-to-[→] ([∧]-elimᵣ (coprimalize-positive)) pos-y₂
    {-
    let
      a = -- TODO: Similar to c, which is normalize-function
        (x₁ ℕ.⌊/⌋₀ (ℕ.gcd x₁ x₂)) ℕ.⌊/⌋₀ (x₂ ℕ.⌊/⌋₀ (ℕ.gcd x₁ x₂)) 🝖[ Id ]-[ coprimalize-quotient-equality{x₁}{x₂} ⦃ {!!} ⦄ ]
        (x₁ ℕ.⌊/⌋₀ x₂)                                             🝖[ Id ]-[ [⌊/⌋₀]-equalityᵣ {x₁}{x₂}{y₁}{y₂} ⦃ {!!} ⦄ ⦃ {!!} ⦄ xy ]
        (y₁ ℕ.⌊/⌋₀ y₂)                                             🝖[ Id ]-[ coprimalize-quotient-equality{y₁}{y₂} ⦃ {!!} ⦄ ]-sym
        (y₁ ℕ.⌊/⌋₀ (ℕ.gcd y₁ y₂)) ℕ.⌊/⌋₀ (y₂ ℕ.⌊/⌋₀ (ℕ.gcd y₁ y₂)) 🝖-end
      b =
        (x₁ ℕ.⌊/⌋₀ (ℕ.gcd x₁ x₂)) ℕ.⋅ (y₂ ℕ.⌊/⌋₀ (ℕ.gcd y₁ y₂)) 🝖[ Id ]-[ [⌊/⌋₀]-equalityₗ {x₁ ℕ.⌊/⌋₀ (ℕ.gcd x₁ x₂)}{x₂ ℕ.⌊/⌋₀ (ℕ.gcd x₁ x₂)}{y₁ ℕ.⌊/⌋₀ (ℕ.gcd y₁ y₂)}{y₂ ℕ.⌊/⌋₀ (ℕ.gcd y₁ y₂)} ⦃ {!!} ⦄ ⦃ {!!} ⦄ {!!} {!!} a ]
        (y₁ ℕ.⌊/⌋₀ (ℕ.gcd y₁ y₂)) ℕ.⋅ (x₂ ℕ.⌊/⌋₀ (ℕ.gcd x₁ x₂)) 🝖-end
      -- c : normalize (x₁ /ₙ x₂) ≡ normalize (y₁ /ₙ y₂)
      c : Id ((x₁ ℕ.⌊/⌋₀ (ℕ.gcd x₁ x₂)) ℕ.⋅ (y₂ ℕ.⌊/⌋₀ (ℕ.gcd y₁ y₂))) ((y₁ ℕ.⌊/⌋₀ (ℕ.gcd y₁ y₂)) ℕ.⋅ (x₂ ℕ.⌊/⌋₀ (ℕ.gcd x₁ x₂)))
      c = normalize-function{x}{y} xy
    in [/ₙ]-equality ⦃ {!!} ⦄ ⦃ {!!} ⦄
      ([⌊/⌋₀]-equalityᵣ {x₁}{ℕ.gcd x₁ x₂}{y₁}{ℕ.gcd y₁ y₂} ⦃ {!!} ⦄ ⦃ {!!} ⦄ $
        (x₁ ℕ.⋅ (ℕ.gcd y₁ y₂)) 🝖[ Id ]-[ {!!} ]
        {!!} 🝖[ Id ]-[ {!!} ]
        {!!} 🝖[ Id ]-[ {!!} ]
        (y₁ ℕ.⋅ (ℕ.gcd x₁ x₂)) 🝖-end
      )
      ([⌊/⌋₀]-equalityᵣ {x₂}{ℕ.gcd x₁ x₂}{y₂}{ℕ.gcd y₁ y₂} ⦃ {!!} ⦄ ⦃ {!!} ⦄ (
        {!!}
        {-([⌊/⌋₀]-equalityₗ {x₂}{ℕ.gcd x₁ x₂}{y₂}{ℕ.gcd y₁ y₂} ⦃ {!!} ⦄ ⦃ {!!} ⦄
          (gcd-dividesᵣ{x₁}{x₂})
          (gcd-dividesᵣ{y₁}{y₂})
          {!!}
        )-}
      ))
    -}
    -- rewrite 
    -- rewrite 
    -- {![⌊/⌋]-of-same 🝖 symmetry(Id) [⌊/⌋]-of-same!}
    -- ((x₁ ℕ.⌊/⌋₀ (ℕ.gcd x₁ x₂)) /ₙ (x₂ ℕ.⌊/⌋₀ (ℕ.gcd x₁ x₂))) ⦃ _ ⦄ 🝖[ Id ]-[ {!!} ]
    -- ((y₁ ℕ.⌊/⌋₀ (ℕ.gcd y₁ y₂)) /ₙ (y₂ ℕ.⌊/⌋₀ (ℕ.gcd y₁ y₂))) ⦃ _ ⦄ 🝖-end
    -- xy : Id (x₁ ℕ.⋅ y₂) (y₁ ℕ.⋅ x₂)

    -- [⌊/⌋]-equality

  {-
    x₁ ℕ.⌊/⌋₀ (ℕ.gcd x₁ x₂) y₁
    x₁ ℕ.⌊/⌋₀ (ℕ.gcd (x₁ y₁) (x₂ y₁))
    x₁ ℕ.⌊/⌋₀ (ℕ.gcd (x₁ y₁) (x₁ y₂))
    x₁ ℕ.⌊/⌋₀ (ℕ.gcd y₁ y₂) x₁
    1 ℕ.⌊/⌋₀ (ℕ.gcd y₁ y₂)
    y₁ ℕ.⌊/⌋₀ (ℕ.gcd y₁ y₂) y₁
  -}

module _ where
  import      Numeral.Natural.Oper as ℕ
  open import Numeral.Natural.Oper.Proofs as ℕ using ()
  open import Structure.Operator
  open import Structure.Operator.Properties
  open import Structure.Relator.Equivalence
  open import Structure.Relator.Properties
  open import Structure.Setoid using (Equiv)
  open import Syntax.Transitivity
  open import Type.Identity
  open import Type.Identity.Proofs

  [𝟏][𝟎]-inequality : Positive(𝟏)
  [𝟏][𝟎]-inequality = <>

  open import Structure.Operator.Proofs.Util
  additiveOp-operator : ∀(_▫_) → ⦃ distᵣ : Distributivityᵣ ⦃ Id-equiv ⦄ (ℕ._⋅_)(_▫_) ⦄ → BinaryOperator(additiveOp(_▫_))
  BinaryOperator.congruence(additiveOp-operator(_▫_)) {x₁ /ₙ y₁} {z₁ /ₙ w₁} {x₂ /ₙ y₂} {z₂ /ₙ w₂} p1 p2 =
    ((x₁ ℕ.⋅ y₂) ▫ (y₁ ℕ.⋅ x₂)) ℕ.⋅ (w₁ ℕ.⋅ w₂)                   🝖[ Id ]-[ distributivityᵣ(ℕ._⋅_)(_▫_) {x₁ ℕ.⋅ y₂}{y₁ ℕ.⋅ x₂}{w₁ ℕ.⋅ w₂} ]
    ((x₁ ℕ.⋅ y₂) ℕ.⋅ (w₁ ℕ.⋅ w₂)) ▫ ((y₁ ℕ.⋅ x₂) ℕ.⋅ (w₁ ℕ.⋅ w₂)) 🝖[ Id ]-[ congruence₂(_▫_) (One.associate-commute4-c{_▫_ = ℕ._⋅_} {x₁}{y₂}{w₁}{w₂}) (One.associate-commute4-c{_▫_ = ℕ._⋅_} {y₁}{x₂}{w₁}{w₂}) ]
    ((x₁ ℕ.⋅ w₁) ℕ.⋅ (y₂ ℕ.⋅ w₂)) ▫ ((y₁ ℕ.⋅ w₁) ℕ.⋅ (x₂ ℕ.⋅ w₂)) 🝖[ Id ]-[ congruence₂(_▫_) (congruence₂(ℕ._⋅_) p1 (commutativity(ℕ._⋅_) {y₂}{w₂})) (congruence₂(ℕ._⋅_) (commutativity(ℕ._⋅_) {y₁}{w₁}) p2) ]
    ((z₁ ℕ.⋅ y₁) ℕ.⋅ (w₂ ℕ.⋅ y₂)) ▫ ((w₁ ℕ.⋅ y₁) ℕ.⋅ (z₂ ℕ.⋅ y₂)) 🝖[ Id ]-[ congruence₂(_▫_) (One.associate-commute4-c{_▫_ = ℕ._⋅_} {z₁}{y₁}{w₂}{y₂}) (One.associate-commute4-c{_▫_ = ℕ._⋅_} {w₁}{y₁}{z₂}{y₂}) ]
    ((z₁ ℕ.⋅ w₂) ℕ.⋅ (y₁ ℕ.⋅ y₂)) ▫ ((w₁ ℕ.⋅ z₂) ℕ.⋅ (y₁ ℕ.⋅ y₂)) 🝖[ Id ]-[ distributivityᵣ(ℕ._⋅_)(_▫_) {z₁ ℕ.⋅ w₂}{w₁ ℕ.⋅ z₂}{y₁ ℕ.⋅ y₂} ]-sym
    ((z₁ ℕ.⋅ w₂) ▫ (w₁ ℕ.⋅ z₂)) ℕ.⋅ (y₁ ℕ.⋅ y₂)                   🝖-end
    where open import Relator.Equals.Proofs.Equiv

  open import Structure.Operator.Proofs.Util
  instance
    [+]-operator : BinaryOperator(_+_)
    [+]-operator = additiveOp-operator(ℕ._+_)
    
  instance
    [⋅]-operator : BinaryOperator(_⋅_)
    BinaryOperator.congruence [⋅]-operator {x₁ /ₙ y₁} {z₁ /ₙ w₁} {x₂ /ₙ y₂} {z₂ /ₙ w₂} p1 p2 =
      (x₁ ℕ.⋅ x₂) ℕ.⋅ (w₁ ℕ.⋅ w₂) 🝖[ Id ]-[ One.associate-commute4-c{_▫_ = ℕ._⋅_} {x₁}{x₂}{w₁}{w₂} ]
      (x₁ ℕ.⋅ w₁) ℕ.⋅ (x₂ ℕ.⋅ w₂) 🝖[ Id ]-[ congruence₂(ℕ._⋅_) p1 p2 ]
      (z₁ ℕ.⋅ y₁) ℕ.⋅ (z₂ ℕ.⋅ y₂) 🝖[ Id ]-[ One.associate-commute4-c{_▫_ = ℕ._⋅_} {z₁}{z₂}{y₁}{y₂} ]-sym
      (z₁ ℕ.⋅ z₂) ℕ.⋅ (y₁ ℕ.⋅ y₂) 🝖-end
      where open import Relator.Equals.Proofs.Equiv

  instance
    [+]-identityₗ : Identityₗ(_+_)(𝟎)
    Identityₗ.proof [+]-identityₗ = reflexivity(Id)

  instance
    [+]-identityᵣ : Identityᵣ(_+_)(𝟎)
    Identityᵣ.proof [+]-identityᵣ = reflexivity(Id)

  instance
    [+]-associativity : Associativity(_+_)
    Associativity.proof [+]-associativity {x₁ /ₙ y₁} {x₂ /ₙ y₂} {x₃ /ₙ y₃} = congruence₂(ℕ._⋅_) l r where
      open import Relator.Equals.Proofs.Equiv
      l =
        (((x₁ ℕ.⋅ y₂) ℕ.+ (y₁ ℕ.⋅ x₂)) ℕ.⋅ y₃) ℕ.+ ((y₁ ℕ.⋅ y₂) ℕ.⋅ x₃)          🝖[ Id ]-[ congruence₂ₗ(ℕ._+_)((y₁ ℕ.⋅ y₂) ℕ.⋅ x₃) (distributivityᵣ(ℕ._⋅_)(ℕ._+_) {x₁ ℕ.⋅ y₂}{y₁ ℕ.⋅ x₂}{y₃}) ]
        (((x₁ ℕ.⋅ y₂) ℕ.⋅ y₃) ℕ.+ ((y₁ ℕ.⋅ x₂) ℕ.⋅ y₃)) ℕ.+ ((y₁ ℕ.⋅ y₂) ℕ.⋅ x₃) 🝖[ Id ]-[ associativity(ℕ._+_) {(x₁ ℕ.⋅ y₂) ℕ.⋅ y₃} {(y₁ ℕ.⋅ x₂) ℕ.⋅ y₃} {(y₁ ℕ.⋅ y₂) ℕ.⋅ x₃} ]
        ((x₁ ℕ.⋅ y₂) ℕ.⋅ y₃) ℕ.+ (((y₁ ℕ.⋅ x₂) ℕ.⋅ y₃) ℕ.+ ((y₁ ℕ.⋅ y₂) ℕ.⋅ x₃)) 🝖[ Id ]-[ congruence₂(ℕ._+_) (associativity(ℕ._⋅_) {x₁} {y₂} {y₃}) (congruence₂(ℕ._+_) (associativity(ℕ._⋅_) {y₁}{x₂}{y₃}) (associativity(ℕ._⋅_) {y₁}{y₂}{x₃})) ]
        (x₁ ℕ.⋅ (y₂ ℕ.⋅ y₃)) ℕ.+ ((y₁ ℕ.⋅ (x₂ ℕ.⋅ y₃)) ℕ.+ (y₁ ℕ.⋅ (y₂ ℕ.⋅ x₃))) 🝖[ Id ]-[ congruence₂ᵣ(ℕ._+_)(x₁ ℕ.⋅ (y₂ ℕ.⋅ y₃)) (distributivityₗ(ℕ._⋅_)(ℕ._+_) {y₁}{x₂ ℕ.⋅ y₃}{y₂ ℕ.⋅ x₃}) ]-sym
        (x₁ ℕ.⋅ (y₂ ℕ.⋅ y₃)) ℕ.+ (y₁ ℕ.⋅ ((x₂ ℕ.⋅ y₃) ℕ.+ (y₂ ℕ.⋅ x₃)))          🝖-end

      r =
        (y₁ ℕ.⋅ (y₂ ℕ.⋅ y₃)) 🝖[ Id ]-[ associativity(ℕ._⋅_) {y₁}{y₂}{y₃} ]-sym
        ((y₁ ℕ.⋅ y₂) ℕ.⋅ y₃) 🝖-end

  instance
    [⋅]-identityₗ : Identityₗ(_⋅_)(𝟏)
    Identityₗ.proof [⋅]-identityₗ = reflexivity(Id)

  instance
    [⋅]-identityᵣ : Identityᵣ(_⋅_)(𝟏)
    Identityᵣ.proof [⋅]-identityᵣ = reflexivity(Id)

  instance
    [⋅]-associativity : Associativity(_⋅_)
    Associativity.proof [⋅]-associativity {x₁ /ₙ y₁} {x₂ /ₙ y₂} {x₃ /ₙ y₃} =
      ((x₁ ℕ.⋅ x₂) ℕ.⋅ x₃) ℕ.⋅ (y₁ ℕ.⋅ (y₂ ℕ.⋅ y₃)) 🝖[ Id ]-[ congruence₂(ℕ._⋅_) (associativity(ℕ._⋅_) {x₁}{x₂}{x₃}) (symmetry(Id) (associativity(ℕ._⋅_) {y₁}{y₂}{y₃})) ]
      (x₁ ℕ.⋅ (x₂ ℕ.⋅ x₃)) ℕ.⋅ ((y₁ ℕ.⋅ y₂) ℕ.⋅ y₃) 🝖-end
        where open import Relator.Equals.Proofs.Equiv

  instance
    [⋅]-commutativity : Commutativity(_⋅_)
    Commutativity.proof [⋅]-commutativity {x₁ /ₙ y₁} {x₂ /ₙ y₂} =
      (x₁ ℕ.⋅ x₂) ℕ.⋅ (y₂ ℕ.⋅ y₁) 🝖[ Id ]-[ congruence₂(ℕ._⋅_) (commutativity(ℕ._⋅_) {x₁}{x₂}) (commutativity(ℕ._⋅_) {y₂}{y₁}) ]
      (x₂ ℕ.⋅ x₁) ℕ.⋅ (y₁ ℕ.⋅ y₂) 🝖-end
      where open import Relator.Equals.Proofs.Equiv

  instance
    [⋅][+]-distributivityₗ : Distributivityₗ(_⋅_)(_+_)
    Distributivityₗ.proof [⋅][+]-distributivityₗ {x₁ /ₙ y₁} {x₂ /ₙ y₂} {x₃ /ₙ y₃} =
      (x₁ ℕ.⋅ ((x₂ ℕ.⋅ y₃) ℕ.+ (y₂ ℕ.⋅ x₃))) ℕ.⋅ ((y₁ ℕ.⋅ y₂) ℕ.⋅ (y₁ ℕ.⋅ y₃))                 🝖[ Id ]-[ congruence₂(ℕ._⋅_) (distributivityₗ(ℕ._⋅_)(ℕ._+_) {x₁}{x₂ ℕ.⋅ y₃}{y₂ ℕ.⋅ x₃}) (One.associate-commute4-c {_▫_ = ℕ._⋅_} {y₁}{y₂}{y₁}{y₃} 🝖 symmetry(Id) (One.associate4-321-222 {_▫_ = ℕ._⋅_} {y₁}{y₁}{y₂}{y₃})) ]
      ((x₁ ℕ.⋅ (x₂ ℕ.⋅ y₃)) ℕ.+ (x₁ ℕ.⋅ (y₂ ℕ.⋅ x₃))) ℕ.⋅ (y₁ ℕ.⋅ (y₁ ℕ.⋅ (y₂ ℕ.⋅ y₃)))        🝖[ Id ]-[ associativity(ℕ._⋅_) {(x₁ ℕ.⋅ (x₂ ℕ.⋅ y₃)) ℕ.+ (x₁ ℕ.⋅ (y₂ ℕ.⋅ x₃))}{y₁}{y₁ ℕ.⋅ (y₂ ℕ.⋅ y₃)} ]-sym
      (((x₁ ℕ.⋅ (x₂ ℕ.⋅ y₃)) ℕ.+ (x₁ ℕ.⋅ (y₂ ℕ.⋅ x₃))) ℕ.⋅ y₁) ℕ.⋅ (y₁ ℕ.⋅ (y₂ ℕ.⋅ y₃))        🝖[ Id ]-[ congruence₂ₗ(ℕ._⋅_)(y₁ ℕ.⋅ (y₂ ℕ.⋅ y₃)) p ]
      ((x₁ ℕ.⋅ x₂) ℕ.⋅ (y₁ ℕ.⋅ y₃) ℕ.+ ((y₁ ℕ.⋅ y₂) ℕ.⋅ (x₁ ℕ.⋅ x₃))) ℕ.⋅ (y₁ ℕ.⋅ (y₂ ℕ.⋅ y₃)) 🝖-end
      where
        open import Relator.Equals.Proofs.Equiv
        p =
          ((x₁ ℕ.⋅ (x₂ ℕ.⋅ y₃)) ℕ.+ (x₁ ℕ.⋅ (y₂ ℕ.⋅ x₃))) ℕ.⋅ y₁          🝖[ Id ]-[ distributivityᵣ(ℕ._⋅_)(ℕ._+_) {x₁ ℕ.⋅ (x₂ ℕ.⋅ y₃)}{x₁ ℕ.⋅ (y₂ ℕ.⋅ x₃)}{y₁} ]
          ((x₁ ℕ.⋅ (x₂ ℕ.⋅ y₃)) ℕ.⋅ y₁) ℕ.+ ((x₁ ℕ.⋅ (y₂ ℕ.⋅ x₃)) ℕ.⋅ y₁) 🝖[ Id ]-[ congruence₂(ℕ._+_) (One.associate4-213-222 {_▫_ = ℕ._⋅_} {x₁}{x₂}{y₃}{y₁} 🝖 congruence₂ᵣ(ℕ._⋅_)(x₁ ℕ.⋅ x₂) (commutativity(ℕ._⋅_) {y₃}{y₁})) (commutativity(ℕ._⋅_) {x₁ ℕ.⋅ (y₂ ℕ.⋅ x₃)}{y₁} 🝖 One.associate4-321-222 {_▫_ = ℕ._⋅_} {y₁}{x₁}{y₂}{x₃} 🝖 One.associate-commute4-c {_▫_ = ℕ._⋅_} {y₁}{x₁}{y₂}{x₃}) ]
          (x₁ ℕ.⋅ x₂) ℕ.⋅ (y₁ ℕ.⋅ y₃) ℕ.+ ((y₁ ℕ.⋅ y₂) ℕ.⋅ (x₁ ℕ.⋅ x₃))   🝖-end

  open import Logic.Propositional
  open import Structure.Operator.Proofs
  instance
    [⋅][+]-distributivityᵣ : Distributivityᵣ(_⋅_)(_+_)
    [⋅][+]-distributivityᵣ = [↔]-to-[→] OneTypeTwoOp.distributivity-equivalence-by-commutativity [⋅][+]-distributivityₗ

  instance
    [⋅][+]-distributivity : Distributivity(_⋅_)(_+_)
    [⋅][+]-distributivity = intro

  open import Functional.Instance
  open import Logic.Predicate
  open import Syntax.Function
  open import Syntax.Implication

  avg₂ : ℚ₊₀ → ℚ₊₀ → ℚ₊₀
  avg₂ x@((x₁ /ₙ x₂) ⦃ pos-x ⦄) y@((y₁ /ₙ y₂) ⦃ pos-y ⦄) =
    (crossMul(ℕ._+_) x y /ₙ (2 ℕ.⋅ (x₂ ℕ.⋅ y₂)))
    ⦃ [↔]-to-[→] (ℕ.[⋅]-positive {a = 2}) ([∧]-intro <> ([↔]-to-[→] ℕ.[⋅]-positive ([∧]-intro pos-x pos-y))) ⦄

  {-
  avg₂-[≤]-lower-bound : ∀{x y} → (x ≤ y) → (x ≤ avg₂ x y)
  avg₂-[≤]-lower-bound x@{x₁ /ₙ x₂} y@{y₁ /ₙ y₂} xy =
    x₁ ℕ.⋅ (2 ℕ.⋅ (x₂ ℕ.⋅ y₂))         🝖[ Id ]-[ {!!} ]-sub
    (2 ℕ.⋅ (x₁ ℕ.⋅ y₂)) ℕ.⋅ x₂         🝖[ ℕ._≤_ ]-[ {!!} ]
    (x₁ ℕ.⋅ y₂ ℕ.+ x₁ ℕ.⋅ y₂) ℕ.⋅ x₂   🝖[ ℕ._≤_ ]-[ {!!} ]
    ((x₁ ℕ.⋅ y₂ ℕ.+ y₁ ℕ.⋅ x₂) ℕ.⋅ x₂) 🝖-end
    where
      import Numeral.Natural.Relation.Order as ℕ
      import Numeral.Natural.Relation.Order.Proofs as ℕ
  -}

  -- avg₂-lower-bound : ∀{x y} → (min x y < avg₂ x y)
  -- avg₂-upper-bound : ∀{x y} → (avg₂ x y < max x y)

  {-
  ℚ₊₀-dense : ∀{x y} → ∃(m ↦ x < m < y)
  ∃.witness (ℚ₊₀-dense {x} {y}) = avg₂ x y
  ∃.proof (ℚ₊₀-dense x@{x₁ /ₙ x₂} y@{y₁ /ₙ y₂}) =
    • {!(x₁ /ₙ x₂) < (((x₁ /ₙ x₂) + (y₁ /ₙ y₂)) / fromℕ 2)!}
    • {!!}
    ⇒₂-[ [∧]-intro ]
    (x < avg₂ x y < y) ⇒-end
  -}

  open import Structure.Operator.Monoid
  open import Structure.Operator.Ring
  import      Numeral.Natural.Oper.Proofs.Structure as ℕ
  instance
    [+]-monoid : Monoid(_+_)
    Monoid.identity-existence [+]-monoid = [∃]-intro 𝟎 ⦃ intro ⦄

  instance
    ℚ₊₀-nonZero : NonIdentityRelation([+]-monoid)
    NonIdentityRelation.NonIdentity ℚ₊₀-nonZero = Positive
    NonIdentityRelation.proof       ℚ₊₀-nonZero = NonIdentityRelation.proof ℕ.ℕ-nonZero
      where open import Relator.Equals.Proofs.Equiv

  instance
    [⋅]-monoid : Monoid(_⋅_)
    Monoid.identity-existence [⋅]-monoid = [∃]-intro 𝟏 ⦃ intro ⦄

  open import Numeral.Natural.Oper.Proofs.Multiplication
  instance
    [+][−₀]-inverseOperatorᵣ : InverseOperatorᵣ(_+_)(_−₀_)
    InverseOperatorᵣ.proof [+][−₀]-inverseOperatorᵣ {x₁ /ₙ x₂} {y₁ /ₙ y₂} =
      ((((x₁ ℕ.⋅ y₂) ℕ.+ (x₂ ℕ.⋅ y₁)) ℕ.⋅ y₂) ℕ.−₀ ((x₂ ℕ.⋅ y₂) ℕ.⋅ y₁)) ℕ.⋅ x₂ 🝖[ Id ]-[ congruence₂ₗ(ℕ._⋅_)(x₂) (congruence₂ᵣ(ℕ._−₀_)(((x₁ ℕ.⋅ y₂) ℕ.+ (x₂ ℕ.⋅ y₁)) ℕ.⋅ y₂) (One.commuteᵣ-assocₗ{_▫_ = ℕ._⋅_} {x₂}{y₂}{y₁})) ]
      ((((x₁ ℕ.⋅ y₂) ℕ.+ (x₂ ℕ.⋅ y₁)) ℕ.⋅ y₂) ℕ.−₀ ((x₂ ℕ.⋅ y₁) ℕ.⋅ y₂)) ℕ.⋅ x₂ 🝖[ Id ]-[ congruence₂ₗ(ℕ._⋅_)(x₂) (distributivityᵣ(ℕ._⋅_)(ℕ._−₀_) {(x₁ ℕ.⋅ y₂) ℕ.+ (x₂ ℕ.⋅ y₁)}{x₂ ℕ.⋅ y₁}{y₂}) ]-sym
      ((((x₁ ℕ.⋅ y₂) ℕ.+ (x₂ ℕ.⋅ y₁)) ℕ.−₀ (x₂ ℕ.⋅ y₁)) ℕ.⋅ y₂) ℕ.⋅ x₂          🝖[ Id ]-[ congruence₂ₗ(ℕ._⋅_)(x₂) (congruence₂ₗ(ℕ._⋅_)(y₂) (inverseOperᵣ(ℕ._+_)(ℕ._−₀_) {x₁ ℕ.⋅ y₂}{x₂ ℕ.⋅ y₁})) ]
      ((x₁ ℕ.⋅ y₂) ℕ.⋅ y₂) ℕ.⋅ x₂                                               🝖[ Id ]-[ One.commuteᵣ-assocₗ{_▫_ = ℕ._⋅_} {x₁ ℕ.⋅ y₂}{y₂}{x₂} ]
      ((x₁ ℕ.⋅ y₂) ℕ.⋅ x₂) ℕ.⋅ y₂                                               🝖[ Id ]-[ congruence₂ₗ(ℕ._⋅_)(y₂) (One.commuteᵣ-assocₗ{_▫_ = ℕ._⋅_} {x₁}{y₂}{x₂}) ]
      ((x₁ ℕ.⋅ x₂) ℕ.⋅ y₂) ℕ.⋅ y₂                                               🝖[ Id ]-[ One.associate4-123-321 {_▫_ = ℕ._⋅_} {x₁}{x₂}{y₂}{y₂} 🝖 One.associate4-321-231 {_▫_ = ℕ._⋅_} {x₁}{x₂}{y₂}{y₂} ]
      x₁ ℕ.⋅ ((x₂ ℕ.⋅ y₂) ℕ.⋅ y₂)                                               🝖-end
      where open import Relator.Equals.Proofs.Equiv

  instance
    [−₀]-operator : BinaryOperator(_−₀_)
    [−₀]-operator = additiveOp-operator(ℕ._−₀_)

  instance
    [+]-commutativity : Commutativity(_+_)
    Commutativity.proof [+]-commutativity {x₁ /ₙ x₂} {y₁ /ₙ y₂} =
      ((x₁ ℕ.⋅ y₂) ℕ.+ (x₂ ℕ.⋅ y₁)) ℕ.⋅ (y₂ ℕ.⋅ x₂) 🝖[ Id ]-[ congruence₂(ℕ._⋅_) (commutativity(ℕ._+_) {x₁ ℕ.⋅ y₂}{x₂ ℕ.⋅ y₁}) (commutativity(ℕ._⋅_) {y₂}{x₂}) ]
      ((x₂ ℕ.⋅ y₁) ℕ.+ (x₁ ℕ.⋅ y₂)) ℕ.⋅ (x₂ ℕ.⋅ y₂) 🝖[ Id ]-[ congruence₂ₗ(ℕ._⋅_)(x₂ ℕ.⋅ y₂) (congruence₂(ℕ._+_) (commutativity(ℕ._⋅_) {x₂}{y₁}) (commutativity(ℕ._⋅_) {x₁}{y₂})) ]
      ((y₁ ℕ.⋅ x₂) ℕ.+ (y₂ ℕ.⋅ x₁)) ℕ.⋅ (x₂ ℕ.⋅ y₂) 🝖-end
      where open import Relator.Equals.Proofs.Equiv

  instance
    [+]-cancellationᵣ : Cancellationᵣ(_+_)
    [+]-cancellationᵣ = OneTypeTwoOp.cancellationᵣ-by-inverseOper

  instance
    [+]-cancellationₗ : Cancellationₗ(_+_)
    [+]-cancellationₗ = [↔]-to-[←] One.cancellation-equivalence-by-commutativity [+]-cancellationᵣ

  import Structure.Operator.Ring.Proofs as Ring

  instance
    [⋅]-absorberₗ : Absorberₗ(_⋅_)(𝟎)
    [⋅]-absorberₗ = Ring.[⋅]-absorberₗ-by-cancellationᵣ ⦃ rg = intro ⦄ ⦃ canc = [+]-cancellationᵣ ⦄ where open Monoid [⋅]-monoid

  instance
    [⋅]-absorberᵣ : Absorberᵣ(_⋅_)(𝟎)
    [⋅]-absorberᵣ = Ring.[⋅]-absorberᵣ-by-cancellationᵣ ⦃ rg = intro ⦄ ⦃ canc = [+]-cancellationᵣ ⦄ where open Monoid [⋅]-monoid

  instance
    [+][⋅]-rig : Rig(_+_)(_⋅_)
    Rig.[+]-monoid    [+][⋅]-rig = [+]-monoid
    Rig.[⋅]-absorberₗ [+][⋅]-rig = [⋅]-absorberₗ
    Rig.[⋅]-absorberᵣ [+][⋅]-rig = [⋅]-absorberᵣ
  open Rig([+][⋅]-rig)

  instance
    [+][⋅]-division : Division(_+_)(_⋅_)
    Division.⅟ [+][⋅]-division = ⅟
    Division.[⋅]-inverseₗ [+][⋅]-division {x /ₙ y} = commutativity(ℕ._⋅_) {x}{y} where open import Relator.Equals.Proofs.Equiv
    Division.[⋅]-inverseᵣ [+][⋅]-division {x /ₙ y} = commutativity(ℕ._⋅_) {y}{x} where open import Relator.Equals.Proofs.Equiv

module _ where
  open import Numeral.Natural.Relation.Divisibility

  Whole : ℚ₊₀ → Type
  Whole(x /ₙ y) = y ∣ x

  open import Logic.Propositional
  open import Numeral.Natural.Relation.Divisibility.Proofs.Product
  open import Numeral.Natural.Coprime
  open import Numeral.Natural.Coprime.Proofs
  open import Structure.Relator.Properties
  open import Type.Identity

  normalized-quotient-whole-has-unit-denominator : ∀{q@(x /ₙ y) : ℚ₊₀} → Coprime x y → Whole(q) → (Id y 1)
  normalized-quotient-whole-has-unit-denominator coprim div = coprime-divides-is-unit div (symmetry(Coprime) coprim)
