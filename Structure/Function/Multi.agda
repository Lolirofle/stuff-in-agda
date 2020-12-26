module Structure.Function.Multi where

open import Data
open import Data.Boolean
open import Data.Tuple.Raise
import      Data.Tuple.Raiseᵣ.Functions as Raise
open import Data.Tuple.RaiseTypeᵣ
import      Data.Tuple.RaiseTypeᵣ.Functions as RaiseType
open import Function.DomainRaise as DomainRaise using (_→̂_)
import      Function.Equals.Multi as Multi
open import Function.Multi
import      Function.Multi.Functions as Multi
open import Functional
open import Lang.Instance
open import Logic
open import Logic.Propositional
open import Logic.Predicate
import      Lvl
import      Lvl.MultiFunctions as Lvl
open import Numeral.Natural
open import Numeral.Natural.Oper.Comparisons
open import Structure.Setoid.Uniqueness
open import Structure.Setoid
open import Syntax.Number
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓₑ ℓₑ₁ ℓₑ₂ ℓₗ : Lvl.Level
private variable n : ℕ

module Names where
  module _ {X : Type{ℓ₁}} {Y : Type{ℓ₂}} ⦃ _ : Equiv{ℓₑ₂}(Y) ⦄ where
    -- Definition of the relation between a function and an operation that says:
    -- The function preserves the operation.
    -- Often used when defining homomorphisms.
    -- Examples:
    --   Preserving(1) (f)(g₁)(g₂)
    --   = (∀{x} → (f ∘₁ g₁)(x) ≡ (g₂ on₁ f)(x))
    --   = (∀{x} → (f(g₁(x)) ≡ g₂(f(x)))
    --   Preserving(2) (f)(g₁)(g₂)
    --   = (∀{x y} → (f ∘₂ g₁)(x)(y) ≡ (g₂ on₂ f)(x)(y))
    --   = (∀{x y} → (f(g₁ x y) ≡ g₂ (f(x)) (f(y)))
    --   Preserving(3) (f)(g₁)(g₂)
    --   = (∀{x y z} → (f ∘₃ g₁)(x)(y)(z) ≡ (g₂ on₃ f)(x)(y)(z))
    --   = (∀{x y z} → (f(g₁ x y z) ≡ g₂ (f(x)) (f(y)) (f(z))))
    -- Alternative implementation:
    --   Preserving(n) (f)(g₁)(g₂) = Multi.Names.⊜₊(n) ([→̂]-to-[⇉] n (f DomainRaise.∘ g₁)) ([→̂]-to-[⇉] n (g₂ DomainRaise.on f))
    Preserving : (n : ℕ) → (f : X → Y) → (X →̂ X)(n) → (Y →̂ Y)(n) → Stmt{if positive?(n) then (ℓ₁ Lvl.⊔ ℓₑ₂) else ℓₑ₂}
    Preserving(𝟎)       (f)(g₁)(g₂) = (f(g₁) ≡ g₂)
    Preserving(𝐒(𝟎))    (f)(g₁)(g₂) = (∀{x} → f(g₁(x)) ≡ g₂(f(x)))
    Preserving(𝐒(𝐒(n))) (f)(g₁)(g₂) = (∀{x} → Preserving(𝐒(n)) (f) (g₁(x)) (g₂(f(x))))

    Preserving₀ = Preserving(0)
    Preserving₁ = Preserving(1)
    Preserving₂ = Preserving(2)
    Preserving₃ = Preserving(3)
    Preserving₄ = Preserving(4)
    Preserving₅ = Preserving(5)
    Preserving₆ = Preserving(6)
    Preserving₇ = Preserving(7)
    Preserving₈ = Preserving(8)
    Preserving₉ = Preserving(9)

  module _ where
    RelationReplacement : ∀{B : Type{ℓ}} → (B → B → Type{ℓₑ}) → (n : ℕ) → ∀{ℓ𝓈 ℓ𝓈ₑ}{As : Types{n}(ℓ𝓈)} → (RaiseType.mapWithLvls(\A ℓₑ → Equiv{ℓₑ}(A)) As ℓ𝓈ₑ) ⇉ᵢₙₛₜ ((As ⇉ B) → (As ⇉ B) → Stmt{Lvl.⨆(ℓ𝓈) Lvl.⊔ ℓₑ Lvl.⊔ Lvl.⨆(ℓ𝓈ₑ)})
    RelationReplacement(_▫_) 0         f g = f ▫ g
    RelationReplacement(_▫_) 1         f g = ∀{x y} → (x ≡ y) → (f(x) ▫ g(y))
    RelationReplacement(_▫_) (𝐒(𝐒(n)))     = Multi.expl-to-inst(𝐒(n)) (Multi.compose(𝐒(n)) (\R f g → ∀{x y} → (x ≡ y) → R (f(x)) (g(y))) (Multi.inst-to-expl(𝐒(n)) (RelationReplacement(_▫_) (𝐒(n)))))

    FunctionReplacement : (n : ℕ) → ∀{ℓ𝓈 ℓ𝓈ₑ}{As : Types{n}(ℓ𝓈)}{B : Type{ℓ}} → (RaiseType.mapWithLvls(\A ℓₑ → Equiv{ℓₑ}(A)) As ℓ𝓈ₑ) ⇉ᵢₙₛₜ (⦃ equiv-B : Equiv{ℓₑ}(B) ⦄ → (As ⇉ B) → (As ⇉ B) → Stmt{Lvl.⨆(ℓ𝓈) Lvl.⊔ ℓₑ Lvl.⊔ Lvl.⨆(ℓ𝓈ₑ)})
    FunctionReplacement 0         f g = f ≡ g
    FunctionReplacement 1         f g = ∀{x y} → (x ≡ y) → (f(x) ≡ g(y))
    FunctionReplacement (𝐒(𝐒(n)))     = Multi.expl-to-inst(𝐒(n)) (Multi.compose(𝐒(n)) (\R ⦃ equiv-B ⦄ f g → ∀{x y} → (x ≡ y) → R ⦃ equiv-B ⦄ (f(x)) (g(y))) (Multi.inst-to-expl(𝐒(n)) (FunctionReplacement (𝐒(n)))))

    -- Generalization of `Structure.Function.Function` for nested function types (or normally known as: functions of any number of arguments (n-ary functions)).
    -- Examples:
    --   Function(0) f g = f ≡ g
    --   Function(1) f g = ∀{x y} → (x ≡ y) → (f(x) ≡ g(y))
    --   Function(2) f g = ∀{x y} → (x ≡ y) → ∀{x₁ y₁} → (x₁ ≡ y₁) → (f(x)(x₁) ≡ g(y)(y₁))
    --   Function(3) f g = ∀{x y} → (x ≡ y) → ∀{x₁ y₁} → (x₁ ≡ y₁) → ∀{x₂ y₂} → (x₂ ≡ y₂) → (f(x)(x₁)(x₂) ≡ g(y)(y₁)(y₂))
    Function : (n : ℕ) → ∀{ℓ𝓈 ℓ𝓈ₑ}{As : Types{n}(ℓ𝓈)}{B : Type{ℓ}} → (RaiseType.mapWithLvls(\A ℓₑ → Equiv{ℓₑ}(A)) As ℓ𝓈ₑ) ⇉ᵢₙₛₜ (⦃ equiv-B : Equiv{ℓₑ}(B) ⦄ → (As ⇉ B) → Stmt)
    Function(n) = Multi.expl-to-inst(n) (Multi.compose(n) (\R ⦃ equiv-B ⦄ → R ⦃ equiv-B ⦄ $₂_) (Multi.inst-to-expl(n) (FunctionReplacement(n))))

  module _ where
    CompatibleReplacement : (n : ℕ) → ∀{ℓ𝓈 ℓ𝓈ₗ}{As : Types{n}(ℓ𝓈)}{B : Type{ℓ}} → (RaiseType.mapWithLvls(\A ℓₗ → A → A → Type{ℓₗ}) As ℓ𝓈ₗ) ⇉ ((B → B → Stmt{ℓₗ}) → (As ⇉ B) → (As ⇉ B) → Stmt{ℓₗ Lvl.⊔ Lvl.⨆(ℓ𝓈) Lvl.⊔ Lvl.⨆(ℓ𝓈ₗ)})
    CompatibleReplacement 0               (_▫_) f g = f ▫ g
    CompatibleReplacement 1         (_▫₀_)(_▫_) f g = ∀{x y} → (x ▫₀ y) → (f(x) ▫ g(y))
    CompatibleReplacement (𝐒(𝐒(n))) (_▫₀_)          = Multi.compose(𝐒(n)) (R ↦ _▫_ ↦ f ↦ g ↦ ∀{x y} → (x ▫₀ y) → R(_▫_) (f(x)) (g(y))) (CompatibleReplacement(𝐒(n)))

    Compatible : (n : ℕ) → ∀{ℓ𝓈 ℓ𝓈ₗ}{As : Types{n}(ℓ𝓈)}{B : Type{ℓ}} → (RaiseType.mapWithLvls(\A ℓₗ → A → A → Type{ℓₗ}) As ℓ𝓈ₗ) ⇉ ((B → B → Stmt{ℓₗ}) → (As ⇉ B) → Stmt)
    Compatible(n) = Multi.compose(n) ((_$₂_) ∘_) (CompatibleReplacement(n))

  module _ {T : Type{ℓ}} ⦃ _ : Equiv{ℓₑ}(T) ⦄ where
    -- Definition of the relation between a function and an operation that says:
    -- The function preserves the operation.
    -- This is a special case of the (_preserves_)-relation that has the same operator inside and outside.
    -- Special cases:
    --   Additive function (Operator is a conventional _+_)
    --   Multiplicative function (Operator is a conventional _*_)
    -- ∀{x y} → (f(x ▫ y) ≡ f(x) ▫ f(y))
    _preserves_ : (T → T) → (T → T → T) → Stmt
    f preserves (_▫_) = Preserving(2) f (_▫_)(_▫_) -- 

module _ {X : Type{ℓ₁}} {Y : Type{ℓ₂}} ⦃ _ : Equiv{ℓₑ₂}(Y) ⦄ where
  module _ (n : ℕ) (f : X → Y) (g₁ : (X →̂ X)(n)) (g₂ : (Y →̂ Y)(n)) where
    record Preserving : Stmt{if positive?(n) then (ℓ₁ Lvl.⊔ ℓₑ₂) else ℓₑ₂} where -- TODO: Is it possible to prove for levels that an if-expression is less if both are less?
      constructor intro
      field proof : Names.Preserving(n) (f)(g₁)(g₂)
    preserving = inst-fn Preserving.proof

  Preserving₀ = Preserving(0)
  Preserving₁ = Preserving(1)
  Preserving₂ = Preserving(2)
  Preserving₃ = Preserving(3)
  Preserving₄ = Preserving(4)
  Preserving₅ = Preserving(5)
  Preserving₆ = Preserving(6)
  Preserving₇ = Preserving(7)
  Preserving₈ = Preserving(8)
  Preserving₉ = Preserving(9)

  preserving₀ = preserving(0)
  preserving₁ = preserving(1)
  preserving₂ = preserving(2)
  preserving₃ = preserving(3)
  preserving₄ = preserving(4)
  preserving₅ = preserving(5)
  preserving₆ = preserving(6)
  preserving₇ = preserving(7)
  preserving₈ = preserving(8)
  preserving₉ = preserving(9)

module _ {T : Type{ℓ}} ⦃ _ : Equiv{ℓₑ}(T) ⦄ (n : ℕ) (f : T → T) (_▫_ : T → T → T) where
  _preserves_ = Preserving(2) (f)(_▫_)(_▫_)

{-
module _ {T : Type{ℓ}} where
  module _ (n : ℕ) {ℓₗ} (_▫_ : T → T → Stmt{ℓₗ}) (f : RaiseType.repeat n T ⇉ T) where
    record Compatible : Stmt{ℓₗ Lvl.⊔ (if positive?(n) then ℓ else Lvl.𝟎)} where
      constructor intro
      field proof : Names.Compatible(n) (_▫_)(f)
    compatible = inst-fn Compatible.proof

  Compatible₀ = Compatible(0)
  Compatible₁ = Compatible(1)
  Compatible₂ = Compatible(2)
  Compatible₃ = Compatible(3)
  Compatible₄ = Compatible(4)
  Compatible₅ = Compatible(5)
  Compatible₆ = Compatible(6)
  Compatible₇ = Compatible(7)
  Compatible₈ = Compatible(8)
  Compatible₉ = Compatible(9)

  compatible₀ = compatible(0)
  compatible₁ = compatible(1)
  compatible₂ = compatible(2)
  compatible₃ = compatible(3)
  compatible₄ = compatible(4)
  compatible₅ = compatible(5)
  compatible₆ = compatible(6)
  compatible₇ = compatible(7)
  compatible₈ = compatible(8)
  compatible₉ = compatible(9)
-}
