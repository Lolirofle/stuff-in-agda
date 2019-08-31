module Structure.Relator.Properties.Proofs where

import      Lvl
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional
open import Logic
open import Logic.Propositional
open import Logic.Propositional.Theorems
open import Structure.Relator.Properties
open import Type

module _ {ℓ₁ ℓ₂} {T : Type{ℓ₁}} {_<_ : T → T → Stmt{ℓ₂}} where
  [asymmetry]-to-irreflexivity : ⦃ _ : Asymmetry(_<_) ⦄ → Irreflexivity(_<_)
  Irreflexivity.proof([asymmetry]-to-irreflexivity) = [→]-redundancy(asymmetry(_<_))
    -- ∀x∀y. (x<y) → ¬(y<x)
    -- ∀x. (x<x) → ¬(x<x)
    -- ∀x. (x<x) → (x<x) → ⊥
    -- ∀x. (x<x) → ⊥

  [irreflexivity,transitivity]-to-asymmetry : ⦃ _ : Irreflexivity(_<_) ⦄ → ⦃ _ : Transitivity(_<_) ⦄ → Asymmetry(_<_)
  Asymmetry.proof([irreflexivity,transitivity]-to-asymmetry) = Tuple.curry(irreflexivity(_<_) ∘ (Tuple.uncurry(transitivity(_<_))))
    -- ∀x. ¬(x<x)
    -- ∀x. (x<x) → ⊥
    --   ∀x∀y∀z. (x<y)∧(y<z) → (x<z)
    --   ∀x∀y. (x<y)∧(y<x) → (x<x)
    --   ∀y. (x<y)∧(y<x) → (x<x)
    -- ∀x∀y. (x<y)∧(y<x) → ⊥
    -- ∀x∀y. (x<y) → (y<x) → ⊥
    -- ∀x∀y. (x<y) → ¬(y<x)

  -- Definition of a total binary operation
  [total]-to-reflexivity : ⦃ _ : ConverseTotal(_<_) ⦄ → Reflexivity(_<_)
  Reflexivity.proof([total]-to-reflexivity) = [∨]-elim id id (converseTotal(_<_))

  -- TODO: https://proofwiki.org/wiki/Definition%3aRelation_Compatible_with_Operation and substitution. Special case for (≡) and function application: ∀(x∊T)∀(y∊T). (x ≡ y) → (∀(f: T→T). f(x) ≡ f(y))
