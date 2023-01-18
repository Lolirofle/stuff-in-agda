{-# OPTIONS --cubical #-}

module Type.Cubical.Quotient where

open import Functional
import      Lvl
open import Structure.Type.Identity
open import Type.Cubical
open import Type.Cubical.Path
open import Type.Cubical.Path.Equality
open import Type
open import Syntax.Function

private variable ℓ ℓₗ : Lvl.Level
private variable T A B : Type{ℓ}
private variable x y : T
private variable P : T → Type{ℓ}
private variable _▫_ : T → T → Type{ℓ}

data Quotient(_▫_ : T → T → Type{ℓ}) : Type{Lvl.of(T) Lvl.⊔ ℓ} where
  class : T → Quotient(_▫_)
  class-extensionalityₗ : Path(class x) (class y) ← (x ▫ y)

open import Type.Cubical.Path
open import Type.Cubical.Path.Proofs
open import Type.Cubical.Path.Univalence
open import Type.Properties.MereProposition
open import Structure.Function
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Structure.Setoid

elim : (P : Quotient(_▫_) → Type{ℓ}) → (c : (x : T) → P(class x)) → (∀{x y} → (xy : x ▫ y) → PathP(\i → P(class-extensionalityₗ xy i)) (c(x)) (c(y))) → ((q : Quotient(_▫_)) → P(q))
elim P pc pe (class x) = pc x
elim P pc pe (class-extensionalityₗ{x}{y} xy i) = pe xy i

-- Constructs a function on a quotient type from a function on a setoid.
-- Note: The following holds by definition: rec f ⦃ p ⦄ ∘ class = f
rec : (f : A → B) → ⦃ Compatible₁(_▫_)(_≡_) f ⦄ → (Quotient(_▫_) → B)
rec f ⦃ intro p ⦄ = elim(const _) f p

module _ (P : Quotient(_▫_) → Type{ℓ}) ⦃ prop-P : ∀{c} → MereProposition(P(c)) ⦄ where
  class-property : (∀{a} → P(class a)) → (∀{c} → P(c))
  class-property p {c} = elim(P)
    (x ↦ p{x})
    (xy ↦ interval-predicate₁-path{Y = P} (class-extensionalityₗ xy)) c

-- TODO: Use Structuve.Function.Surjective when it is generalized to support Type.Cubical.Logic.∃. The difference is that Type.Cubical.Logic.∃ is a mere propositions while surjective uses existence defined as Σ which is not
open import Type.Cubical.Logic
class-surjective : ∀{y} → ∃(x ↦ class{_▫_ = _▫_} x ≡ y)
class-surjective{_▫_ = _▫_} = class-property(y ↦ ∃(x ↦ class{_▫_ = _▫_} x ≡ y))
  (\{a} → [∃]-intro a ⦃ reflexivity(_≡_) ⦄)

module _ ⦃ equivalence : Equivalence(_▫_) ⦄ ⦃ prop : ∀{x y} → MereProposition(x ▫ y) ⦄ where
  open import BidirectionalFunction using (intro ; _$ₗ_ ; _$ᵣ_)
  open import Type.Cubical.Logic.Extensionality

  class-extensionalityᵣ : (class{_▫_ = _▫_} x ≡ class y) → (x ▫ y)
  class-extensionalityᵣ {x = x} {y = y} p = sub₂(_≡_)(_→ᶠ_) xx-xy (reflexivity(_▫_)) where
    instance
      compat : Compatible₁(_▫_)(Path) (x ▫_)
      compat = intro \ab → propositional-extensionality $ₗ ([↔]-intro (swap(transitivity(_▫_)) (symmetry(_▫_) ab)) (swap(transitivity(_▫_)) ab))

    xx-xy : (x ▫ x) ≡ (x ▫ y)
    xx-xy i = rec(x ▫_) (p i)

  class-extensionality : (class{_▫_ = _▫_} x ≡ class y) ↔ (x ▫ y)
  class-extensionality = intro class-extensionalityₗ class-extensionalityᵣ

module Syntax where
  _/_ : (T : Type{ℓ}) → (T → T → Type{ℓₗ}) → Type
  _ / (_▫_) = Quotient(_▫_)

  [_] : T → (T / (_▫_))
  [_] = class
