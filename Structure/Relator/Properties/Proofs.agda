module Structure.Relator.Properties.Proofs {ℓ₁}{ℓ₂} where

import      Lvl
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Logic.Propositional.Theorems{ℓ₁ Lvl.⊔ ℓ₂}
open import Structure.Relator.Properties{ℓ₁}{ℓ₂}

[asymmetry]-to-irreflexivity : ∀{T}{_<_} → ⦃ _ : Asymmetry{T}(_<_) ⦄ → Irreflexivity{T}(_<_)
irreflexivity ⦃ [asymmetry]-to-irreflexivity ⦄ = [→]-redundancy(asymmetry)
  -- ∀x∀y. (x<y) → ¬(y<x)
  -- ∀x. (x<x) → ¬(x<x)
  -- ∀x. (x<x) → (x<x) → ⊥
  -- ∀x. (x<x) → ⊥

[irreflexivity,transitivity]-to-asymmetry : ∀{T}{_<_} → ⦃ _ : Irreflexivity{T}(_<_) ⦄ → ⦃ _ : Transitivity{T}(_<_) ⦄ → Asymmetry{T}(_<_)
asymmetry ⦃ [irreflexivity,transitivity]-to-asymmetry ⦄ = Tuple.curry(irreflexivity ∘ (Tuple.uncurry transitivity))
  -- ∀x. ¬(x<x)
  -- ∀x. (x<x) → ⊥
  --   ∀x∀y∀z. (x<y)∧(y<z) → (x<z)
  --   ∀x∀y. (x<y)∧(y<x) → (x<x)
  --   ∀y. (x<y)∧(y<x) → (x<x)
  -- ∀x∀y. (x<y)∧(y<x) → ⊥
  -- ∀x∀y. (x<y) → (y<x) → ⊥
  -- ∀x∀y. (x<y) → ¬(y<x)

-- Definition of a total binary operation
[total]-to-reflexivity : ∀{T}{_<_} → ⦃ _ : ConverseTotal{T}(_<_) ⦄ → Reflexivity{T}(_<_)
reflexivity ⦃ [total]-to-reflexivity ⦄ = [∨]-elim id id converseTotal

-- TODO: https://proofwiki.org/wiki/Definition%3aRelation_Compatible_with_Operation and substitution. Special case for (≡) and function application: ∀(x∊T)∀(y∊T). (x ≡ y) → (∀(f: T→T). f(x) ≡ f(y))
