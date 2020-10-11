module Type.Size.Proofs where

import      Lvl
open import Data
open import Data.Proofs
open import Functional
open import Function.Equals
open import Function.Inverseᵣ
open import Function.Inverse
open import Function.Proofs
open import Logic
open import Logic.IntroInstances
open import Logic.Propositional
open import Logic.Predicate
open import Structure.Setoid.WithLvl
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Function.Domain.Proofs
open import Structure.Relator.Equivalence
open import Structure.Relator.Ordering
open import Structure.Relator.Properties
open import Type
import      Type.Size

private variable ℓ ℓ₁ ℓ₂ ℓₑ ℓₑ₁ ℓₑ₂ ℓₑ₃ : Lvl.Level
private variable T A B C : Type{ℓ}

module _ ⦃ equiv : Equiv{ℓₑ}(T) ⦄ where
  open Type.Size

  [≼]-maximum : (_≼_ T (T → T) ⦃ [⊜]-equiv ⦄)
  [≼]-maximum = [∃]-intro(const) ⦃ intro(proof) ⦄ where
    proof : ∀{x y} → (const(x) ⊜ const(y)) → (x ≡ y)
    proof{x}{y} (intro fneq) = fneq{x}

  [≍]-reflexivity-raw : (T ≍ T)
  [≍]-reflexivity-raw = [∃]-intro(id) ⦃ id-bijective ⦄

  [≼]-reflexivity-raw : (T ≼ T)
  [≼]-reflexivity-raw = [∃]-intro(id) ⦃ id-injective ⦄

  [≽]-reflexivity-raw : (T ≽ T)
  [≽]-reflexivity-raw = [∃]-intro(id) ⦃ id-surjective ⦄

  [≼]-minimum-raw : ⦃ equiv-empty : Equiv{ℓₑ₁}(Empty{ℓ}) ⦄ → (_≼_ Empty ⦃ equiv-empty ⦄ T)
  [≼]-minimum-raw = [∃]-intro(empty) ⦃ empty-injective ⦄

    -- TODO: Impossible because there are no functions of type (T → ⊥)?
    -- instance
    --   [≽]-minimum : Weak.Properties.Maximum(_≽_ {ℓ})(Empty)
    --   Weak.Properties.Maximum.proof([≽]-minimum) {T} {}

module _ ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄ ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄ where
  open Type.Size

  [≍]-to-[≼] : (A ≍ B) → (A ≼ B)
  [≍]-to-[≼] ([∃]-intro(f) ⦃ f-bijective ⦄) =
    ([∃]-intro(f) ⦃ bijective-to-injective(f) ⦃ f-bijective ⦄ ⦄)

  [≍]-to-[≽] : (A ≍ B) → (A ≽ B)
  [≍]-to-[≽] ([∃]-intro(f) ⦃ f-bijective ⦄) =
    ([∃]-intro(f) ⦃ bijective-to-surjective(f) ⦃ f-bijective ⦄ ⦄)

  [≽]-to-[≼] : (ab@([∃]-intro f) : (A ≽ B)) → ⦃ func : Function(f) ⦄ ⦃ inv-func : Function(invᵣ-surjective f) ⦄ → (B ≼ A)
  [≽]-to-[≼] ([∃]-intro(f) ⦃ f-surjective ⦄) ⦃ inv-func ⦄ = [∃]-intro(invᵣ f ⦃ surjective-to-invertibleᵣ ⦄) ⦃ inverseᵣ-injective{f = f} ⦃ [∧]-elimᵣ([∃]-proof surjective-to-invertibleᵣ) ⦄ ⦄

  {-[≼]-to-[≽] : (A ≼ B) → (B ≽ A)
  [≼]-to-[≽] ([∃]-intro(f) ⦃ f-injective ⦄) =
    {![∃]-intro()!}
  -}

  [≍]-symmetry-raw : (ab@([∃]-intro f) : (A ≍ B)) → ⦃ func : Function(f) ⦄ → (B ≍ A)
  [≍]-symmetry-raw ([∃]-intro(f) ⦃ f-bijective ⦄)
    = [∃]-intro(inv f ⦃ bijective-to-invertible ⦄) ⦃ inv-bijective{f = f} ⦃ inver = bijective-to-invertible ⦄ ⦄

module _ ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄ ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄ ⦃ equiv-C : Equiv{ℓₑ₃}(C) ⦄ where
  open Type.Size

  [≍]-transitivity-raw : (ab@([∃]-intro f) : (A ≍ B)) ⦃ func-f : Function(f) ⦄ → (bc@([∃]-intro g) : (B ≍ C)) ⦃ func-g : Function(g) ⦄ → (A ≍ C)
  [≍]-transitivity-raw ([∃]-intro(f) ⦃ f-bijective ⦄) ([∃]-intro(g) ⦃ g-bijective ⦄)
    = [∃]-intro(g ∘ f) ⦃ [∘]-bijective {f = g} {g = f} ⦃ g-bijective ⦄ ⦃ f-bijective ⦄ ⦄

  [≼]-transitivity-raw : (A ≼ B) → (B ≼ C) → (A ≼ C)
  [≼]-transitivity-raw ([∃]-intro(f) ⦃ f-injective ⦄) ([∃]-intro(g) ⦃ g-injective ⦄)
    = [∃]-intro(g ∘ f) ⦃ [∘]-injective {f = g}{g = f} ⦃ g-injective ⦄ ⦃ f-injective ⦄ ⦄

  [≽]-transitivity-raw : (A ≽ B) → (([∃]-intro g) : (B ≽ C)) ⦃ func-g : Function(g) ⦄ → (A ≽ C)
  [≽]-transitivity-raw ([∃]-intro(f) ⦃ f-surjective ⦄) ([∃]-intro(g) ⦃ g-surjective ⦄)
    = [∃]-intro(g ∘ f) ⦃ [∘]-surjective {f = g} {g = f} ⦃ g-surjective ⦄ ⦃ f-surjective ⦄ ⦄

module _ where
  open import Relator.Equals renaming (_≡_ to _≡ₑ_)
  open import Relator.Equals.Proofs

  private
    _≍_ : ∀{ℓ₁ ℓ₂} → (A : Type{ℓ₁}) → (B : Type{ℓ₂}) → Stmt
    _≍_ A B = Type.Size._≍_ A B

    _≼_ : ∀{ℓ₁ ℓ₂} → (A : Type{ℓ₁}) → (B : Type{ℓ₂}) → Stmt
    _≼_ A B = Type.Size._≼_ A B

    _≽_ : ∀{ℓ₁ ℓ₂} → (A : Type{ℓ₁}) → (B : Type{ℓ₂}) → Stmt
    _≽_ A B = Type.Size._≽_ A B

    _≭_ : ∀{ℓ₁ ℓ₂} → (A : Type{ℓ₁}) → (B : Type{ℓ₂}) → Stmt
    _≭_ A B = Type.Size._≭_ A B

    _≺_ : ∀{ℓ₁ ℓ₂} → (A : Type{ℓ₁}) → (B : Type{ℓ₂}) → Stmt
    _≺_ A B = Type.Size._≺_ A B

    _≻_ : ∀{ℓ₁ ℓ₂} → (A : Type{ℓ₁}) → (B : Type{ℓ₂}) → Stmt
    _≻_ A B = Type.Size._≻_ A B

  module _ {ℓ} where
    instance
      [≍]-reflexivity : Reflexivity(_≍_ {ℓ})
      [≍]-reflexivity = intro [≍]-reflexivity-raw

    instance
      [≍]-symmetry : Symmetry(_≍_ {ℓ})
      [≍]-symmetry = intro(f ↦ [≍]-symmetry-raw f)

    instance
      [≍]-transitivity : Transitivity(_≍_ {ℓ})
      [≍]-transitivity = intro(f ↦ g ↦ [≍]-transitivity-raw f g)

    instance
      [≍]-equivalence : Equivalence(_≍_ {ℓ})
      [≍]-equivalence = intro

    instance
      [≼]-reflexivity : Reflexivity(_≼_ {ℓ})
      [≼]-reflexivity = intro [≼]-reflexivity-raw

    instance
      [≼]-transitivity : Transitivity(_≼_ {ℓ})
      [≼]-transitivity = intro [≼]-transitivity-raw

    instance
      [≽]-reflexivity : Reflexivity(_≽_ {ℓ})
      [≽]-reflexivity = intro [≽]-reflexivity-raw

    instance
      [≽]-transitivity : Transitivity(_≽_ {ℓ})
      [≽]-transitivity = intro(p ↦ q ↦ [≽]-transitivity-raw p q)

    instance
      [≼]-minimum : Weak.Properties.LE.Minimum(_≼_ {ℓ})(Empty)
      Weak.Properties.Extremumₗ.proof [≼]-minimum = [≼]-minimum-raw

    -- TODO: Impossible because there are no functions of type (T → ⊥)?
    -- instance
    --   [≽]-minimum : Weak.Properties.Maximum(_≽_ {ℓ})(Empty)
    --   Weak.Properties.Maximum.proof([≽]-minimum) {T} {}

  -- TODO: Remove this and the similar one in the other module. A more general variant is defined in Relator.Equals.Proofs
  module _ {A : Type{ℓ}} {B : Type{ℓ}} where
    [≡]-to-[≍] : (A ≡ₑ B) → (A ≍ B)
    [≡]-to-[≍] [≡]-intro = reflexivity(_≍_)
