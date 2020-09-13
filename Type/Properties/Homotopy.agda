module Type.Properties.Homotopy where

open import Functional using (id)
open import Function.Axioms
import      Lvl
open import Logic
open import Logic.Propositional
open import Numeral.Natural
open import Structure.Setoid.WithLvl
open import Type
open import Type.Dependent
open import Type.Properties.Empty
open import Type.Properties.MereProposition
open import Type.Properties.Singleton.Proofs
open import Type.Properties.Singleton
open import Syntax.Function

private variable ℓ ℓ₁ ℓ₂ ℓₑ : Lvl.Level
private variable T A B : Type{ℓ}
private variable P : A → Type{ℓ}
private variable n : ℕ

module _ ⦃ equiv : ∀{ℓ}{T : Type{ℓ}} → Equiv{ℓ}(T) ⦄ where
  HomotopyLevel : ℕ → (A : Type{ℓ}) → Type
  HomotopyLevel(𝟎)      (A) = Σ(A)(x ↦ ∀{y} → (y ≡ x))
  HomotopyLevel(𝐒(𝟎))   (A) = ∀{x y : A} → (x ≡ y)
  HomotopyLevel(𝐒(𝐒(n)))(A) = ∀{x y : A} → HomotopyLevel(𝐒(n))(x ≡ y)

  Truncation : ℕ → (A : Type{ℓ}) → Type
  Truncation(n) = HomotopyLevel(𝐒(𝐒(n)))



  HomotopyLevel-zero-step-is-one : (∀{x y : A} → HomotopyLevel(0)(x ≡ y)) → HomotopyLevel(1)(A)
  HomotopyLevel-zero-step-is-one p {x}{y} = Σ.left(p{x}{y})

  HomotopyLevel-step-is-successor : (∀{x y : A} → HomotopyLevel(n)(x ≡ y)) → HomotopyLevel(𝐒(n))(A)
  HomotopyLevel-step-is-successor {n = 𝟎}    = HomotopyLevel-zero-step-is-one
  HomotopyLevel-step-is-successor {n = 𝐒(n)} = id

  module _
    ⦃ funcExt : ∀{ℓ₁ ℓ₂}{A : Type{ℓ₁}}{P : A → Stmt{ℓ₂}} → DependentImplicitFunctionExtensionality(A)(P) ⦄
    ⦃ prop-eq : ∀{ℓ}{A : Type{ℓ}}{x y : A} → MereProposition(x ≡ y) ⦄
    where

    HomotopyLevel-prop₊ : MereProposition(HomotopyLevel(𝐒(n))(A))
    HomotopyLevel-prop₊ {𝟎}    = prop-universal ⦃ prop-p = prop-universal ⦃ prop-p = prop-eq ⦄ ⦄
    HomotopyLevel-prop₊ {𝐒(n)} = prop-universal ⦃ prop-p = prop-universal ⦃ prop-p = HomotopyLevel-prop₊ {n} ⦄ ⦄

  module _
    (base₁ : ∀{ℓ}{A : Type{ℓ}} → HomotopyLevel(1)(A) → HomotopyLevel(2)(A))
    where

    HomotopyLevel-one-is-zero-step : HomotopyLevel(1)(A) → (∀{x y : A} → HomotopyLevel(0)(x ≡ y))
    HomotopyLevel-one-is-zero-step h1 {x} {y} = intro h1 (base₁ h1)

    HomotopyLevel-successor-step : HomotopyLevel(𝐒(n))(A) → (∀{x y : A} → HomotopyLevel(n)(x ≡ y))
    HomotopyLevel-successor-step {n = 𝟎}    = HomotopyLevel-one-is-zero-step
    HomotopyLevel-successor-step {n = 𝐒(n)} = id

    HomotopyLevel-successor : HomotopyLevel(n)(A) → HomotopyLevel(𝐒(n))(A)
    HomotopyLevel-successor {n = 0} h0         = MereProposition.uniqueness(unit-is-prop ⦃ proof = intro (Σ.left h0) (Σ.right h0) ⦄)
    HomotopyLevel-successor {n = 1}            = base₁
    HomotopyLevel-successor {n = 𝐒(𝐒(n))} hssn = HomotopyLevel-successor {n = 𝐒(n)} hssn

    {- TODO: The zero case needs assumptions about the sigma type because it is not a mere proposition unless both A and equality are mere propositions. So first, prove if equality on the sigma type depends only on its components, and its types are mere propositions, then the sigma type is a mere proposition. Secondly, one can use that proof here
    HomotopyLevel-prop : MereProposition(HomotopyLevel(n)(A))
    HomotopyLevel-prop {𝟎} = intro {!!}
    HomotopyLevel-prop {𝐒 n} = {!!}
    -}

-- TODO: Where should this be stated?
-- ExcludedMiddle : (A : Type{ℓ}) ⦃ equiv-A : Equiv{ℓₑ}(A) ⦄ → Stmt
-- ExcludedMiddle(A) = MereProposition(A) → (IsUnit(A) ∨ IsEmpty(A))
