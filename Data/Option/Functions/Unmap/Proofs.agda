module Data.Option.Functions.Unmap.Proofs where

import      Lvl
open import Data
open import Data.Option
open import Data.Option.Equiv as Option
open import Data.Option.Functions
open import Data.Option.Functions.Unmap
open import Data.Option.Proofs
open import Function.Names using (_⊜_)
open import Functional
open import Lang.Inspect
open import Logic.Predicate
open import Logic.Propositional
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Function.Domain.Proofs
open import Structure.Relator.Properties
open import Structure.Setoid
open import Syntax.Transitivity
open import Type
open import Type.Size

private variable ℓ ℓₑ₁ ℓₑ₂ ℓₑₒ₁ ℓₑₒ₂ : Lvl.Level
private variable T A B : Type{ℓ}

module _
  ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄
  ⦃ equiv-optA : Equiv{ℓₑₒ₁}(Option(A)) ⦄
  ⦃ ext-A : Extensionality equiv-optA ⦄
  ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄
  ⦃ equiv-optB : Equiv{ℓₑₒ₂}(Option(B)) ⦄
  ⦃ ext-B : Extensionality equiv-optB ⦄
  {f : A → B} ⦃ inj-f : Injective(f) ⦄
  where

  unmap-map-inverse : unmap(map f) ⦃ map-injective ⦄ ⊜ f
  unmap-map-inverse = unmap-intro(map f) ⦃ map-injective ⦄ (\x Fx → Fx ≡ f(x))
    (\ab → symmetry(_≡_) (injective(Some) ab))
    (\_ no → [⊥]-elim (Option.cases-inequality no))

module _
  ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄
  ⦃ equiv-optA : Equiv{ℓₑₒ₁}(Option(A)) ⦄
  ⦃ ext-A : Extensionality equiv-optA ⦄
  ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄
  ⦃ equiv-optB : Equiv{ℓₑₒ₂}(Option(B)) ⦄
  ⦃ ext-B : Extensionality equiv-optB ⦄
  {f : Option(A) → Option(B)} ⦃ inj-f : Injective(f) ⦄
  (f-preserve-none : f(None) ≡ None)
  (f-preserve-some : ∀{x} → (f(Some x) ≡ Some(unmap f(x))))
  where

  map-unmap-inverse : map(unmap f) ⊜ f
  map-unmap-inverse {None} =
    map(unmap f) None 🝖[ _≡_ ]-[]
    None              🝖[ _≡_ ]-[ f-preserve-none ]-sym
    f(None)           🝖-end
  map-unmap-inverse {Some x} =
    map(unmap f) (Some x) 🝖[ _≡_ ]-[]
    Some(unmap f(x))      🝖[ _≡_ ]-[ f-preserve-some ]-sym
    f(Some x)             🝖-end

module _
  ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄
  ⦃ equiv-optA : Equiv{ℓₑₒ₁}(Option(A)) ⦄
  ⦃ ext-A : Extensionality equiv-optA ⦄
  ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄
  ⦃ equiv-optB : Equiv{ℓₑₒ₂}(Option(B)) ⦄
  ⦃ ext-B : Extensionality equiv-optB ⦄
  where

  module _ {f : Option(A) → Option(B)} ⦃ inj-f : Injective(f) ⦄ where
    unmap-injective : Injective(unmap f)
    Injective.proof unmap-injective = unmap-intro f (\x Fx → ∀{y} → (Fx ≡ unmap f(y)) → (x ≡ y))
      (\{x₁}{y₁} p₁ → unmap-intro f (\x₂ Fx₂ → (y₁ ≡ Fx₂) → (x₁ ≡ x₂))
        (\{x₂}{y₂} p₂ y₁y₂ → injective(Some) $ injective(f) $
          f(Some x₁) 🝖[ _≡_ ]-[ p₁ ]
          Some y₁    🝖[ _≡_ ]-[ congruence₁(Some) y₁y₂ ]
          Some y₂    🝖[ _≡_ ]-[ p₂ ]-sym
          f(Some x₂) 🝖-end
        )
        (\{x₂}{y₂} p₂ p₃ y₁y₂ → [⊥]-elim $ Option.cases-inequality $ injective(f) $
          f None     🝖[ _≡_ ]-[ p₃ ]
          Some y₂    🝖[ _≡_ ]-[ congruence₁(Some) y₁y₂ ]-sym
          Some y₁    🝖[ _≡_ ]-[ p₁ ]-sym
          f(Some x₁) 🝖-end
        )
      )
      (\{x₁}{y₁} p₁ p₂ → unmap-intro f (\x₂ Fx₂ → (y₁ ≡ Fx₂) → (x₁ ≡ x₂))
        (\{x₂}{y₂} p₃ y₁y₂ → [⊥]-elim $ Option.cases-inequality $ injective(f) $
          f None     🝖[ _≡_ ]-[ p₂ ]
          Some y₁    🝖[ _≡_ ]-[ congruence₁(Some) y₁y₂ ]
          Some y₂    🝖[ _≡_ ]-[ p₃ ]-sym
          f(Some x₂) 🝖-end
        )
        (\{x₂}{y₂} p₃ p₄ y₁y₂ → injective(Some) $ injective(f) $
          f(Some x₁) 🝖[ _≡_ ]-[ p₁ ]
          None       🝖[ _≡_ ]-[ p₃ ]-sym
          f(Some x₂) 🝖-end
        )
      )

  Option-[≼]-injective : (Option(A) ≼ Option(B)) → (A ≼ B)
  Option-[≼]-injective ([∃]-intro f ⦃ p ⦄) = [∃]-intro (unmap f) ⦃ unmap-injective ⦄

module _
  ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄
  ⦃ equiv-optA : Equiv{ℓₑₒ₁}(Option(A)) ⦄
  ⦃ ext-A : Extensionality equiv-optA ⦄
  ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄
  ⦃ equiv-optB : Equiv{ℓₑₒ₂}(Option(B)) ⦄
  ⦃ ext-B : Extensionality equiv-optB ⦄

  {f   : Option(A) → Option(B)}
  {f⁻¹ : Option(A) ← Option(B)}
  ⦃ func : Function(f) ⦄
  ⦃ inj : Injective(f) ⦄
  ⦃ inverᵣ : Inverseᵣ(f)(f⁻¹) ⦄
  where

  private
    F = unmap f
    F⁻¹ = unmap f⁻¹ ⦃ inverseᵣ-injective ⦄

  unmap-inverseᵣ : Inverseᵣ(F)(F⁻¹)
  Inverseᵣ.proof unmap-inverseᵣ = unmap-intro f⁻¹ ⦃ _ ⦄ (\x y → F(y) ≡ x)
    (\{y}{x} p₁ → unmap-intro f ⦃ _ ⦄ (\xx Fx → _≡_ xx x → Fx ≡ y)
      (\{a}{b} p₂ p₃ → injective(Some) $
        Some b         🝖[ _≡_ ]-[ p₂ ]-sym
        f(Some a)      🝖[ _≡_ ]-[ congruence₁(f) (congruence₁(Some) p₃) ]
        f(Some x)      🝖[ _≡_ ]-[ congruence₁(f) p₁ ]-sym
        f(f⁻¹(Some y)) 🝖[ _≡_ ]-[ inverseᵣ(f)(f⁻¹) ]
        Some y         🝖-end
      )
      (\{a}{b} p₂ p₃ p₄ → [⊥]-elim $ Option.cases-inequality $
        None           🝖[ _≡_ ]-[ p₂ ]-sym
        f(Some a)      🝖[ _≡_ ]-[ congruence₁(f) (congruence₁(Some) p₄) ]
        f(Some x)      🝖[ _≡_ ]-[ congruence₁(f) p₁ ]-sym
        f(f⁻¹(Some y)) 🝖[ _≡_ ]-[ inverseᵣ(f)(f⁻¹) ]
        Some y         🝖-end
      )
      (reflexivity(_≡_))
    )
    (\{y}{x} p₁ p₂ → unmap-intro f ⦃ _ ⦄ (\xx Fx → _≡_ xx x → Fx ≡ y)
      (\{a}{b} p₃ p₄ → [⊥]-elim $ Option.cases-inequality $
        None         🝖[ _≡_ ]-[ inverseᵣ(f)(f⁻¹) ]-sym
        f(f⁻¹(None)) 🝖[ _≡_ ]-[ congruence₁(f) p₂ ]
        f(Some x)    🝖[ _≡_ ]-[ congruence₁(f) (congruence₁(Some) p₄) ]-sym
        f(Some a)    🝖[ _≡_ ]-[ p₃ ]
        Some b       🝖-end)
      (\{a}{b} p₃ p₄ p₅ → injective(Some) $
        Some b         🝖[ _≡_ ]-[ p₄ ]-sym
        f(None)        🝖[ _≡_ ]-[ congruence₁(f) p₁ ]-sym
        f(f⁻¹(Some y)) 🝖[ _≡_ ]-[ inverseᵣ(f)(f⁻¹) ]
        Some y         🝖-end
      )
      (reflexivity(_≡_))
    )
