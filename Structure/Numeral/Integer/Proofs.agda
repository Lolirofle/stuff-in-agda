module Structure.Numeral.Integer.Proofs where

open import Data.Either
open import Functional
open import Logic.Propositional
import      Lvl
open import Structure.Numeral.Integer
open import Structure.Relator
open import Structure.Relator.Proofs
open import Structure.Relator.Properties
open import Structure.Setoid.WithLvl
open import Structure.Operator.Ring
open import Structure.OrderedField
open import Type

private variable ℓₒ ℓₗ ℓₑ ℓₗ₁ ℓₗ₂ : Lvl.Level
private variable Z : Type{ℓₒ}
private variable _+_ _⋅_ : Z → Z → Z
private variable _≤_ : Z → Z → Type{ℓₗ}

module _ ⦃ equiv : Equiv{ℓₑ}(Z) ⦄ ⦃ int : Integer ⦃ equiv ⦄ (_+_)(_⋅_)(_≤_) ⦄ where
  open Integer(int)

  negative-induction : ∀{ℓ}{P : Z → Type{ℓ}} ⦃ rel-p : UnaryRelator(P) ⦄ → P(𝟎) → (∀{n} → (n ≤ 𝟎) → P(n) → P(𝐏(n))) → (∀{n} → (n ≤ 𝟎) → P(n))
  negative-induction {P = P} pz ps {n} neg =
    substitute₁(P) [−−]-elim (positive-induction
      {P = P ∘ (−_)}
      ⦃ [∘]-unaryRelator ⦄
      (substitute₁ₗ(P) [−]-of-𝟎 pz)
      (\{n} pos pnn → substitute₁ₗ(P) [+]-negation-distribution (ps{− n} ([≤]-flip-positive pos) pnn))
      {− n}
      ([↔]-to-[→] [≤]-flip-negative neg)
    )

  induction : ∀{ℓ}{P : Z → Type{ℓ}} ⦃ rel-p : UnaryRelator(P) ⦄ → P(𝟎) → (∀{n} → (n ≤ 𝟎) → P(n) → P(𝐏(n))) → (∀{n} → (𝟎 ≤ n) → P(n) → P(𝐒(n))) → (∀{n} → P(n))
  induction pz pp ps {n} with converseTotal(_≤_) {n}{𝟎}
  ... | Left  neg = negative-induction pz pp neg
  ... | Right pos = positive-induction pz ps pos

  

  {- TODO: Not here. Needs invertible mult
  record Exponentiation(_^_ : Z → Z → Z) : Type{ℓₑ Lvl.⊔ Lvl.of(Z) Lvl.⊔ Lvl.of(𝟎 ≤ 𝟎)} where
    field
      base : ∀{a} → (a ^ 𝟎 ≡ 𝟏)
      step : ∀{a b} → (𝟎 ≤ b) → (a ^ (b + 𝟏) ≡ a ⋅ (a ^ b))
      neg  : ∀{a b} → (𝟎 ≤ 𝟎) → (a ^ (− b) ≡ ⅟(a ^ b))
  -}
