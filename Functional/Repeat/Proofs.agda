module Functional.Repeat.Proofs where

import Lvl
open import Functional
import      Functional.Names as Names
open import Functional.Repeat
open import Functional.Proofs
open import Logic.Propositional
open import Logic.Predicate
open import Numeral.Natural
open import Structure.Relator.Properties
open import Structure.Function.Domain
open import Type

module _ where
  open import Sets.Setoid

  module _ {ℓ} {X : Type{ℓ}} ⦃ _ : Equiv(X) ⦄ where  
    [^]-from-[∘]-proof : ∀{ℓ₂}{P : (X → X) → Type{ℓ₂}} → (∀{f g : X → X} → P(f ∘ g)) → ∀{f : X → X}{n} → P(f ^ n)
    [^]-from-[∘]-proof {P = P} p {f} {𝟎}   = p{id}{id}
    [^]-from-[∘]-proof {P = P} p {f} {𝐒 n} = p{f}{f ^ n}

    [^]-injective-raw : ∀{f : X → X} → Names.Injective(f) → ∀{n} → Names.Injective(f ^ n)
    [^]-injective-raw inj-f {𝟎}    fnxfny = fnxfny
    [^]-injective-raw inj-f {𝐒(n)} fnxfny = [^]-injective-raw inj-f {n} (inj-f fnxfny)

    [^]-injective : ∀{f : X → X} → ⦃ _ : Injective(f) ⦄ → ∀{n} → Injective(f ^ n)
    Injective.proof ([^]-injective ⦃ intro inj-f ⦄ {n}) = [^]-injective-raw inj-f {n}

    [^]-surjective-raw : ∀{f : X → X} → Names.Surjective(f) → ∀{n} → Names.Surjective(f ^ n)
    [^]-surjective-raw surj-f {𝟎}    {y} = [∃]-intro y ⦃ reflexivity(_≡_) ⦄
    [^]-surjective-raw surj-f {𝐒(n)} {y} = [∃]-intro {!y!} ⦃ {!!} ⦄ -- [^]-surjective-raw inj-f {n} (inj-f fnxfny)

    [^]-surjective : ∀{f : X → X} → ⦃ _ : Surjective(f) ⦄ → ∀{n} → Surjective(f ^ n)
    Surjective.proof ([^]-surjective ⦃ intro inj-f ⦄ {n}) = [^]-surjective-raw inj-f {n}

module _ {ℓ₁}{ℓ₂} {X : Type{ℓ₁}} {Y : Type{ℓ₂}} where
  open import Relator.Equals
  open import Relator.Equals.Proofs


  repeatᵣₗ-flip-equality : ∀{n : ℕ}{_▫_ : Y → X → Y}{init : Y}{x : X} → (repeatᵣ n (swap(_▫_)) x init ≡ repeatₗ n (_▫_) init x)
  repeatᵣₗ-flip-equality {𝟎}               = [≡]-intro
  repeatᵣₗ-flip-equality {𝐒(n)}{_▫_}{_}{x} = [≡]-with(_▫ x) (repeatᵣₗ-flip-equality {n})

  repeatₗᵣ-flip-equality : ∀{n : ℕ}{_▫_ : X → Y → Y}{x : X}{init : Y} → (repeatₗ n (swap _▫_) init x ≡ repeatᵣ n (_▫_) x init)
  repeatₗᵣ-flip-equality {n}{_▫_}{x}{init} = symmetry(_≡_) (repeatᵣₗ-flip-equality {n}{swap _▫_}{init}{x})

module _ {ℓ} {X : Type{ℓ}} where
  open import Relator.Equals
  open import Relator.Equals.Proofs

  -- repeat-equality : ∀{n : ℕ}{X : Type}{_▫_ : X → X → X}{x : X} → ⦃ _ : Commutativity(_▫_) ⦄ → (repeatₗ n (_▫_) x x ≡ repeatᵣ n (_▫_) x x)
  -- repeat-equality : ∀{n : ℕ}{X : Type}{_▫_ : X → X → X}{x init : X} → ⦃ _ : Commutativity(_▫_) ⦄ ⦃ _ : Identity(_▫_)(init) ⦄ → (repeatₗ n (_▫_) init x ≡ repeatᵣ n (_▫_) x init)

  repeat-raise-equality : ∀{n : ℕ}{_▫_ : X → X → X}{elem x : X} → (repeatᵣ n (_▫_) elem (x) ≡ ((elem ▫_) ^ n)(x))
  repeat-raise-equality{𝟎}                     = [≡]-intro
  repeat-raise-equality{𝐒(n)}{_▫_}{elem}{x} = [≡]-with(elem ▫_) (repeat-raise-equality{n}{_▫_}{elem}{x})

  raise-repeat-equality : ∀{n : ℕ}{f : X → X} → (f ^ n ≡ repeatᵣ n (_∘_) f id)
  raise-repeat-equality{𝟎}          = [≡]-intro
  raise-repeat-equality{𝐒(n)}{f} = [≡]-with(f ∘_) (raise-repeat-equality{n}{f})

{- TODO
x ▫₂ n = repeatₗ n (_▫_) init x
(a ▫₂ n₁) ▫₂ n₂ = (a ▫₂ n₂) ▫₂ n₁
a ▫₂ (n₁ + n₂) = (a ▫₂ n₁) ▫₂ n₂
Commutativity(_▫_) → Associativity(_▫_) → Identity(_▫_)(id) → ((a ▫ b) ▫₂ n = (a ▫₂ n) ▫ (b ▫₂ n))
Identity(_▫_)(id) → (id ▫₂ n = id)
-}
