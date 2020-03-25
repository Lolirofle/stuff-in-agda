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
private variable T : Type{ℓ}
private variable _<_ _≡_ : T → T → Stmt{ℓ}

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

-- TODO: https://proofwiki.org/wiki/Definition%3aRelation_Compatible_with_Operation and substitution. Special case for (≡) and function application: ∀(x∊T)∀(y∊T). (x ≡ y) → (∀(f: T→T). f(x) ≡ f(y))
