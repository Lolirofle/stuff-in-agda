module Structure.Relator.Properties.Proofs where

import      Lvl
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Function
open import Functional
open import Logic
-- open import Logic.Classical
open import Logic.Propositional
open import Logic.Propositional.Theorems
open import Structure.Relator.Properties
open import Structure.Relator
open import Structure.Setoid
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓₑ : Lvl.Level
private variable T A B : Type{ℓ}
private variable _<_ _▫_ _▫₁_ _▫₂_ : T → T → Stmt{ℓ}
private variable f : T → T

[asymmetry]-to-irreflexivity : ⦃ _ : Asymmetry(_<_) ⦄ → Irreflexivity(_<_)
Irreflexivity.proof([asymmetry]-to-irreflexivity {_<_ = _<_}) = [→]-redundancy(asymmetry(_<_))

[irreflexivity,transitivity]-to-asymmetry : ⦃ irrefl : Irreflexivity(_<_) ⦄ ⦃ trans : Transitivity(_<_) ⦄ → Asymmetry(_<_)
Asymmetry.proof([irreflexivity,transitivity]-to-asymmetry {_<_ = _<_}) = Tuple.curry(irreflexivity(_<_) ∘ (Tuple.uncurry(transitivity(_<_))))

converseTotal-to-reflexivity : ⦃ convTotal : ConverseTotal(_<_) ⦄ → Reflexivity(_<_)
Reflexivity.proof(converseTotal-to-reflexivity {_<_ = _<_}) = [∨]-elim id id (converseTotal(_<_))

reflexivity-to-negated-irreflexivity : ⦃ refl : Reflexivity(_<_) ⦄ → Irreflexivity((¬_) ∘₂ (_<_))
Irreflexivity.proof (reflexivity-to-negated-irreflexivity {_<_ = _<_}) irrefl = irrefl(reflexivity(_<_))

negated-symmetry : ⦃ sym : Symmetry(_<_) ⦄ → Symmetry((¬_) ∘₂ (_<_))
Symmetry.proof (negated-symmetry {_<_ = _<_}) nxy yx = nxy(symmetry(_<_) yx)

antisymmetry-irreflexivity-to-asymmetry : ⦃ equiv : Equiv{ℓₑ}(T) ⦄ ⦃ rel : BinaryRelator{A = T}(_<_) ⦄ ⦃ antisym : Antisymmetry(_<_)(_≡_) ⦄ ⦃ irrefl : Irreflexivity(_<_) ⦄ → Asymmetry(_<_)
Asymmetry.proof (antisymmetry-irreflexivity-to-asymmetry {_<_ = _<_}) xy yx = irreflexivity(_<_) (substitute₂-₂ᵣ(_<_)(_) (antisymmetry(_<_)(_≡_) xy yx) yx)

asymmetry-to-antisymmetry : ⦃ asym : Asymmetry(_<_) ⦄ → Antisymmetry(_<_)(_▫_)
Antisymmetry.proof (asymmetry-to-antisymmetry {_<_ = _<_}) ab ba = [⊥]-elim(asymmetry(_<_) ab ba)

subrelation-transitivity-to-subtransitivityₗ : ⦃ sub : (_▫₁_) ⊆₂ (_▫₂_) ⦄ ⦃ trans : Transitivity(_▫₂_) ⦄ → Subtransitivityₗ(_▫₂_)(_▫₁_)
Subtransitivityₗ.proof (subrelation-transitivity-to-subtransitivityₗ {_▫₁_ = _▫₁_} {_▫₂_ = _▫₂_}) xy yz = transitivity(_▫₂_) (sub₂(_▫₁_)(_▫₂_) xy) yz

subrelation-transitivity-to-subtransitivityᵣ : ⦃ sub : (_▫₁_) ⊆₂ (_▫₂_) ⦄ ⦃ trans : Transitivity(_▫₂_) ⦄ → Subtransitivityᵣ(_▫₂_)(_▫₁_)
Subtransitivityᵣ.proof (subrelation-transitivity-to-subtransitivityᵣ {_▫₁_ = _▫₁_} {_▫₂_ = _▫₂_}) xy yz = transitivity(_▫₂_) xy (sub₂(_▫₁_)(_▫₂_) yz)

-- TODO: https://proofwiki.org/wiki/Definition%3aRelation_Compatible_with_Operation and substitution. Special case for (≡) and function application: ∀(x∊T)∀(y∊T). (x ≡ y) → (∀(f: T→T). f(x) ≡ f(y))

instance
  -- A subrelation of a reflexive relation is reflexive.
  -- ∀{_□_ _△_ : T → T → Type} → ((_□_) ⊆₂ (_△_)) → (Reflexivity(_□_) → Reflexivity(_△_))
  subrelation-reflexivity : (_⊆₂_) ⊆₂ ((_→ᶠ_) on₂ Reflexivity{ℓ₂ = ℓ}{T = T})
  _⊆₂_.proof subrelation-reflexivity (intro ab) (intro ra) = intro (ab ra)

instance
  -- The negation of a subrelation is a superrelation (contrapositive of binary relations).
  -- ∀{_□_ _△_ : T → T → Type} → ((_□_) ⊆₂ (_△_)) → (((¬_) ∘₂ (_△_)) ⊆₂ ((¬_) ∘₂ (_□_)))
  swapped-negated-subrelation : (_⊆₂_ {A = A}{B = B}{ℓ₁ = ℓ}) ⊆₂ ((_⊇₂_) on₂ ((¬_) ∘₂_))
  _⊆₂_.proof (_⊆₂_.proof swapped-negated-subrelation (intro sub)) = _∘ sub

swap-reflexivity : ⦃ refl : Reflexivity(_▫_) ⦄ → Reflexivity(swap(_▫_))
swap-reflexivity {_▫_ = _▫_} = intro(reflexivity(_▫_))

swap-asymmetry : ⦃ asym : Asymmetry(_▫_) ⦄ → Asymmetry(swap(_▫_))
swap-asymmetry {_▫_ = _▫_} = intro(asymmetry(_▫_))

swap-antisymmetry : ⦃ antisym : Antisymmetry(_▫₁_)(_▫₂_) ⦄ → Antisymmetry(swap(_▫₁_))(_▫₂_)
swap-antisymmetry {_▫₁_ = _▫₁_}{_▫₂_ = _▫₂_} = intro(swap(antisymmetry(_▫₁_)(_▫₂_)))

swap-transitivity : ⦃ trans : Transitivity(_▫_) ⦄ → Transitivity(swap(_▫_))
swap-transitivity {_▫_ = _▫_} = intro(swap(transitivity(_▫_)))

swap-converseTotal : ⦃ tot : ConverseTotal(_▫_) ⦄ → ConverseTotal(swap(_▫_))
swap-converseTotal {_▫_ = _▫_} = intro([∨]-symmetry(converseTotal(_▫_)))

swap-irreflexivity : ⦃ irrefl : Irreflexivity(_▫_) ⦄ → Irreflexivity(swap(_▫_))
swap-irreflexivity {_▫_ = _▫_} = intro(irreflexivity(_▫_))

swap-converseTrichotomy : ⦃ tri : ConverseTrichotomy(_▫₁_)(_▫₂_) ⦄ → ⦃ sym : Symmetry(_▫₂_) ⦄ → ConverseTrichotomy(swap(_▫₁_))(_▫₂_)
swap-converseTrichotomy {_▫₁_ = _▫₁_}{_▫₂_ = _▫₂_} = intro([∨]-symmetry ([∨]-elim2 id ([∨]-elim2 id (symmetry(_▫₂_))) ([∨]-symmetry (trichotomy(_▫₁_)(_▫₂_)))))

on₂-reflexivity : ∀{_▫_ : B → B → Stmt{ℓ}}{f : A → B} → ⦃ refl : Reflexivity(_▫_) ⦄ → Reflexivity((_▫_) on₂ f)
on₂-reflexivity {_▫_ = _▫_} = intro(reflexivity(_▫_))

on₂-symmetry : ∀{_▫_ : B → B → Stmt{ℓ}}{f : A → B} → ⦃ sym : Symmetry(_▫_) ⦄ → Symmetry((_▫_) on₂ f)
on₂-symmetry {_▫_ = _▫_} = intro(symmetry(_▫_))

on₂-transitivity : ∀{_▫_ : B → B → Stmt{ℓ}}{f : A → B} → ⦃ trans : Transitivity(_▫_) ⦄ → Transitivity((_▫_) on₂ f)
on₂-transitivity {_▫_ = _▫_} = intro(transitivity(_▫_))
