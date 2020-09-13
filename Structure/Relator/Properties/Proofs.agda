module Structure.Relator.Properties.Proofs where

import      Lvl
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional
open import Logic
open import Logic.Propositional
open import Logic.Propositional.Theorems
import      Relator.Equals as Equals
open import Structure.Relator.Properties
open import Type

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable T A B : Type{ℓ}
private variable _<_ _≡_ _▫_ _▫₁_ _▫₂_ : T → T → Stmt{ℓ}
private variable f : T → T

[asymmetry]-to-irreflexivity : ⦃ _ : Asymmetry(_<_) ⦄ → Irreflexivity(_<_)
Irreflexivity.proof([asymmetry]-to-irreflexivity {_<_ = _<_}) = [→]-redundancy(asymmetry(_<_))
  -- ∀x∀y. (x<y) → ¬(y<x)
  -- ∀x. (x<x) → ¬(x<x)
  -- ∀x. (x<x) → (x<x) → ⊥
  -- ∀x. (x<x) → ⊥

[irreflexivity,transitivity]-to-asymmetry : ⦃ _ : Irreflexivity(_<_) ⦄ → ⦃ _ : Transitivity(_<_) ⦄ → Asymmetry(_<_)
Asymmetry.proof([irreflexivity,transitivity]-to-asymmetry {_<_ = _<_}) = Tuple.curry(irreflexivity(_<_) ∘ (Tuple.uncurry(transitivity(_<_))))
  -- ∀x. ¬(x<x)
  -- ∀x. (x<x) → ⊥
  --   ∀x∀y∀z. (x<y)∧(y<z) → (x<z)
  --   ∀x∀y. (x<y)∧(y<x) → (x<x)
  --   ∀y. (x<y)∧(y<x) → (x<x)
  -- ∀x∀y. (x<y)∧(y<x) → ⊥
  -- ∀x∀y. (x<y) → (y<x) → ⊥
  -- ∀x∀y. (x<y) → ¬(y<x)

[total]-to-reflexivity : ⦃ _ : ConverseTotal(_<_) ⦄ → Reflexivity(_<_)
Reflexivity.proof([total]-to-reflexivity {_<_ = _<_}) = [∨]-elim id id (converseTotal(_<_))

negated-reflexivity-irreflexivity : ⦃ _ : Reflexivity(_<_) ⦄ → Irreflexivity(¬_ ∘₂ _<_)
Irreflexivity.proof (negated-reflexivity-irreflexivity {_<_ = _<_}) irrefl = irrefl(reflexivity(_<_))

negated-symmetry : ⦃ _ : Symmetry(_<_) ⦄ → Symmetry(¬_ ∘₂ _<_)
Symmetry.proof (negated-symmetry {_<_ = _<_}) nxy yx = nxy(symmetry(_<_) yx)

antisymmetry-irreflexivity-to-asymmetry : ⦃ _ : Antisymmetry(_<_)(Equals._≡_) ⦄ → ⦃ _ : Irreflexivity(_<_) ⦄ → Asymmetry(_<_)
Asymmetry.proof (antisymmetry-irreflexivity-to-asymmetry {_<_ = _<_}) xy yx with Equals.[≡]-intro ← antisymmetry(_<_)(Equals._≡_) xy yx = irreflexivity(_<_) xy

asymmetry-to-antisymmetry : ⦃ _ : Asymmetry(_<_) ⦄ → Antisymmetry(_<_)(Equals._≡_)
Antisymmetry.proof (asymmetry-to-antisymmetry {_<_ = _<_}) ab ba = [⊥]-elim(asymmetry(_<_) ab ba)

subrelation-transitivity-to-subtransitivityₗ : ⦃ _ : (_▫₁_) ⊆₂ (_▫₂_) ⦄ ⦃ _ : Transitivity(_▫₂_) ⦄ → Subtransitivityₗ(_▫₂_)(_▫₁_)
Subtransitivityₗ.proof (subrelation-transitivity-to-subtransitivityₗ {_▫₁_ = _▫₁_} {_▫₂_ = _▫₂_}) xy yz = transitivity(_▫₂_) (sub₂(_▫₁_)(_▫₂_) xy) yz

subrelation-transitivity-to-subtransitivityᵣ : ⦃ _ : (_▫₁_) ⊆₂ (_▫₂_) ⦄ ⦃ _ : Transitivity(_▫₂_) ⦄ → Subtransitivityᵣ(_▫₂_)(_▫₁_)
Subtransitivityᵣ.proof (subrelation-transitivity-to-subtransitivityᵣ {_▫₁_ = _▫₁_} {_▫₂_ = _▫₂_}) xy yz = transitivity(_▫₂_) xy (sub₂(_▫₁_)(_▫₂_) yz)

-- TODO: https://proofwiki.org/wiki/Definition%3aRelation_Compatible_with_Operation and substitution. Special case for (≡) and function application: ∀(x∊T)∀(y∊T). (x ≡ y) → (∀(f: T→T). f(x) ≡ f(y))

instance
  subrelation-reflexivity : (_⊆₂_ {ℓ₁ = ℓ}{T = T}) ⊆₂ ((_→ᶠ_) on₂ Reflexivity)
  _⊆₂_.proof subrelation-reflexivity (intro ab) (intro ra) = intro (ab ra)

on₂-reflexivity : ∀{_▫_ : B → B → Stmt{ℓ}}{f : A → B} → ⦃ refl : Reflexivity(_▫_) ⦄ → Reflexivity((_▫_) on₂ f)
on₂-reflexivity {_▫_ = _▫_} = intro(reflexivity(_▫_))

swap-reflexivity : ⦃ refl : Reflexivity(_▫_) ⦄ → Reflexivity(swap(_▫_))
swap-reflexivity {_▫_ = _▫_} = intro(reflexivity(_▫_))
