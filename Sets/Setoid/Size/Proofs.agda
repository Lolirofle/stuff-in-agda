module Sets.Setoid.Size.Proofs where

import      Lvl
open import Functional
open import Functional.Proofs
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Sets.Setoid
open import Sets.Setoid.Size
open import Structure.Function.Domain
open import Structure.Function.Domain.Proofs
open import Structure.Relator.Equivalence
open import Structure.Relator.Ordering
open import Structure.Relator.Properties
open import Type

module _ {ℓ} where
  [≍]-to-[≼] : ∀{A B : Setoid{ℓ}} → (A ≍ B) → (A ≼ B)
  [≍]-to-[≼] ([∃]-intro(f) ⦃ [∧]-intro f-function f-bijective ⦄) =
    ([∃]-intro(f) ⦃ [∧]-intro f-function (bijective-to-injective(f) ⦃ f-bijective ⦄) ⦄)

module _ {ℓ} where
  [≍]-to-[≽] : ∀{A B : Setoid{ℓ}} → (A ≍ B) → (A ≽ B)
  [≍]-to-[≽] ([∃]-intro(f) ⦃ [∧]-intro f-function f-bijective ⦄) =
    ([∃]-intro(f) ⦃ [∧]-intro f-function (bijective-to-surjective(f) ⦃ f-bijective ⦄) ⦄)

-- module _ {ℓ} where
--   [≽]-to-[≼] : ∀{A B : Setoid{ℓ}} → (A ≽ B) → (B ≼ A)
--   [≽]-to-[≼] ([∃]-intro(f) ⦃ [∧]-intro f-function f-surjective ⦄) =
--     ([∃]-intro(inv-fnᵣ f) ⦃ [∧]-intro (TODO: f-function) (invᵣ-injective ⦃ f-surjective ⦄) ⦄)
-- TODO: This would need a proof of: inverse-existence-choice : (∀{y} → ∃(x ↦ y ≡ f(x))) → ∃{Obj = Y → X}(choice ↦ Function(choice) ∧ ∀{y} → y ≡ f(choice(y))). In other words, the "extensional axiom of choice"? Is it valid in Agda? https://plato.stanford.edu/entries/type-theory-intuitionistic/

module _ {ℓ} where
  instance
    [≍]-reflexivity : Reflexivity(_≍_ {ℓ})
    Reflexivity.proof([≍]-reflexivity) = [∃]-intro(id) ⦃ [∧]-intro id-function id-bijective ⦄

module _ {ℓ} where
  instance
    [≍]-symmetry : Symmetry(_≍_ {ℓ})
    Symmetry.proof([≍]-symmetry) ([∃]-intro(f) ⦃ [∧]-intro f-function f-bijective ⦄)
      = [∃]-intro(inv-fn f ⦃ f-bijective ⦄) ⦃ [∧]-intro
          (inv-function{f = f} ⦃ f-function ⦄ ⦃ f-bijective ⦄)
          (inv-bijective{f = f} ⦃ f-function ⦄ ⦃ f-bijective ⦄)
        ⦄

module _ {ℓ} where
  instance
    [≍]-transitivity : Transitivity(_≍_ {ℓ})
    Transitivity.proof([≍]-transitivity) ([∃]-intro(f) ⦃ [∧]-intro f-function f-bijective ⦄) ([∃]-intro(g) ⦃ [∧]-intro g-function g-bijective ⦄)
      = [∃]-intro(g ∘ f) ⦃ [∧]-intro
          ([∘]-function  {f = g}{g = f} ⦃ g-function ⦄ ⦃ f-function ⦄)
          ([∘]-bijective {f = g} ⦃ g-function ⦄ {g = f} ⦃ g-bijective ⦄ ⦃ f-bijective ⦄)
        ⦄

module _ {ℓ} where
  instance
    [≍]-equivalence : Equivalence(_≍_ {ℓ})
    [≍]-equivalence = intro

module _ {ℓ} where
  instance
    [≼]-reflexivity : Reflexivity(_≼_ {ℓ})
    Reflexivity.proof([≼]-reflexivity) = [∃]-intro(id) ⦃ [∧]-intro id-function id-injective ⦄

module _ {ℓ} where
  instance
    [≼]-transitivity : Transitivity(_≼_ {ℓ})
    Transitivity.proof([≼]-transitivity) ([∃]-intro(f) ⦃ [∧]-intro f-function f-injective ⦄) ([∃]-intro(g) ⦃ [∧]-intro g-function g-injective ⦄)
      = [∃]-intro(g ∘ f) ⦃ [∧]-intro
          ([∘]-function  {f = g}{g = f} ⦃ g-function ⦄ ⦃ f-function ⦄)
          ([∘]-injective {f = g}{g = f} ⦃ g-injective ⦄ ⦃ f-injective ⦄)
        ⦄

module _ {ℓ} where
  instance
    [≽]-reflexivity : Reflexivity(_≽_ {ℓ})
    Reflexivity.proof([≽]-reflexivity) = [∃]-intro(id) ⦃ [∧]-intro id-function id-surjective ⦄

module _ {ℓ} where
  instance
    [≽]-transitivity : Transitivity(_≽_ {ℓ})
    Transitivity.proof([≽]-transitivity) ([∃]-intro(f) ⦃ [∧]-intro f-function f-surjective ⦄) ([∃]-intro(g) ⦃ [∧]-intro g-function g-surjective ⦄)
      = [∃]-intro(g ∘ f) ⦃ [∧]-intro
          ([∘]-function  {f = g}{g = f} ⦃ g-function ⦄ ⦃ f-function ⦄)
          ([∘]-surjective {f = g} ⦃ g-function ⦄ {g = f} ⦃ g-surjective ⦄ ⦃ f-surjective ⦄)
        ⦄
