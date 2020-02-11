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
open import Logic.Propositional
open import Logic.Predicate
import      Sets.Setoid
open import Structure.Function.Domain
open import Structure.Function.Domain.Proofs
open import Structure.Relator.Equivalence
open import Structure.Relator.Ordering
open import Structure.Relator.Properties
open import Type
import      Type.Size

module _ {ℓ} {T : Type{ℓ}} ⦃ _ : Sets.Setoid.Equiv(T) ⦄ where
  open Sets.Setoid
  open Type.Size

  [≼]-maximum : (_≼_ T (T → T) ⦃ [⊜]-equiv ⦄)
  [≼]-maximum = [∃]-intro(const) ⦃ intro(proof) ⦄ where
    proof : ∀{x y} → (const(x) ⊜ const(y)) → (x ≡ y)
    proof{x}{y} (intro fneq) = fneq{x}

module _ where
  open import Relator.Equals
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

  module _ {ℓ₁ ℓ₂} {A : Type{ℓ₁}} {B : Type{ℓ₂}} where
    [≍]-to-[≼] : (A ≍ B) → (A ≼ B)
    [≍]-to-[≼] ([∃]-intro(f) ⦃ f-bijective ⦄) =
      ([∃]-intro(f) ⦃ bijective-to-injective(f) ⦃ f-bijective ⦄ ⦄)

    [≍]-to-[≽] : (A ≍ B) → (A ≽ B)
    [≍]-to-[≽] ([∃]-intro(f) ⦃ f-bijective ⦄) =
      ([∃]-intro(f) ⦃ bijective-to-surjective(f) ⦃ f-bijective ⦄ ⦄)

    [≽]-to-[≼] : (A ≽ B) → (B ≼ A)
    [≽]-to-[≼] ([∃]-intro(f) ⦃ f-surjective ⦄) =
      ([∃]-intro(invᵣ f) ⦃ invᵣ-injective{f = f} ⦃ f-surjective ⦄ ⦄)

    {-[≼]-to-[≽] : (A ≼ B) → (B ≽ A)
    [≼]-to-[≽] ([∃]-intro(f) ⦃ f-injective ⦄) =
      {![∃]-intro()!}
    -}

  module _ {ℓ} where
    instance
      [≍]-reflexivity : Reflexivity(_≍_ {ℓ})
      Reflexivity.proof([≍]-reflexivity) = [∃]-intro(id) ⦃ id-bijective ⦄

    instance
      [≍]-symmetry : Symmetry(_≍_ {ℓ})
      Symmetry.proof([≍]-symmetry) ([∃]-intro(f) ⦃ f-bijective ⦄)
        = [∃]-intro(inv f ⦃ f-bijective ⦄) ⦃
            (inv-bijective{f = f} ⦃ f-bijective ⦄)
          ⦄

    instance
      [≍]-transitivity : Transitivity(_≍_ {ℓ})
      Transitivity.proof([≍]-transitivity) ([∃]-intro(f) ⦃ f-bijective ⦄) ([∃]-intro(g) ⦃ g-bijective ⦄)
        = [∃]-intro(g ∘ f) ⦃
            ([∘]-bijective {f = g} {g = f} ⦃ g-bijective ⦄ ⦃ f-bijective ⦄)
          ⦄

    instance
      [≍]-equivalence : Equivalence(_≍_ {ℓ})
      [≍]-equivalence = intro

    instance
      [≼]-reflexivity : Reflexivity(_≼_ {ℓ})
      Reflexivity.proof([≼]-reflexivity) = [∃]-intro(id) ⦃ id-injective ⦄

    instance
      [≼]-transitivity : Transitivity(_≼_ {ℓ})
      Transitivity.proof([≼]-transitivity) ([∃]-intro(f) ⦃ f-injective ⦄) ([∃]-intro(g) ⦃ g-injective ⦄)
        = [∃]-intro(g ∘ f) ⦃
            ([∘]-injective {f = g}{g = f} ⦃ g-injective ⦄ ⦃ f-injective ⦄)
          ⦄

    instance
      [≽]-reflexivity : Reflexivity(_≽_ {ℓ})
      Reflexivity.proof([≽]-reflexivity) = [∃]-intro(id) ⦃ id-surjective ⦄

    instance
      [≽]-transitivity : Transitivity(_≽_ {ℓ})
      Transitivity.proof([≽]-transitivity) ([∃]-intro(f) ⦃ f-surjective ⦄) ([∃]-intro(g) ⦃ g-surjective ⦄)
        = [∃]-intro(g ∘ f) ⦃
            ([∘]-surjective {f = g} {g = f} ⦃ g-surjective ⦄ ⦃ f-surjective ⦄)
          ⦄

    instance
      [≼]-minimum : Weak.Properties.Minimum(_≼_ {ℓ})(Empty)
      Weak.Properties.Minimum.proof([≼]-minimum) = [∃]-intro(empty) ⦃ empty-injective ⦄

    -- TODO: Impossible because there are no functions of type (T → ⊥)?
    -- instance
    --   [≽]-minimum : Weak.Properties.Maximum(_≽_ {ℓ})(Empty)
    --   Weak.Properties.Maximum.proof([≽]-minimum) {T} {}

  module _ {ℓ} {A : Type{ℓ}} {B : Type{ℓ}} where
    [≡]-to-[≍] : (A ≡ B) → (A ≍ B)
    [≡]-to-[≍] [≡]-intro = reflexivity(_≍_)
