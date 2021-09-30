{-# OPTIONS --cubical #-}

module Type.Cubical.Quotient where

open import Functional
import      Lvl
open import Structure.Type.Identity
open import Type.Cubical
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
  class-extensionalityₗ : (class x ≡ class y) ← (x ▫ y)

open import Type.Cubical.Path
open import Type.Cubical.Univalence
open import Type.Properties.MereProposition
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties

module _ (P : Quotient(_▫_) → Type{ℓ}) ⦃ prop-P : ∀{c} → MereProposition(P(c)) ⦄ where
  Quotient-property-pathP : ∀{x y}{px : P(x)}{py : P(y)} → (xy : x ≡ y) → PathP(\i → P(xy i)) px py
  Quotient-property-pathP {x}{y}{px}{py} xy = IdentityEliminator.elim Path-identity-eliminator (xy ↦ (∀{px}{py} → PathP(\i → P(xy i)) px py)) (\{c} → uniqueness(P(c))) {x}{y} xy {px}{py}

  class-property : (∀{a} → P(class a)) → (∀{c} → P(c))
  class-property p {class a} = p{a}
  class-property p {class-extensionalityₗ {x} {y} xy i} = Quotient-property-pathP {px = p{x}}{py = p{y}} (class-extensionalityₗ xy) i

-- TODO: Use Structuve.Function.Surjective when it is generalized to support Type.Cubical.Logic.∃. The difference is that Type.Cubical.Logic.∃ is a mere propositions while surjective uses existence defined as Σ which is not
open import Type.Cubical.Logic
class-surjective : ∀{y} → ∃(x ↦ class{_▫_ = _▫_} x ≡ y)
class-surjective{_▫_ = _▫_} = class-property(y ↦ ∃(x ↦ class{_▫_ = _▫_} x ≡ y)) (\{a} → [∃]-intro a ⦃ reflexivity(_≡_) ⦄)

-- Note: The following holds by definition: ∀{P : (A → B) → Type{ℓ}}{f}{p} → P(f) → P(Quotient-recursion f p ∘ class).
Quotient-recursion : (f : A → B) → (∀{a b} → (a ▫ b) → (f(a) ≡ f(b))) → (Quotient(_▫_) → B)
Quotient-recursion f _ (class x) = f(x)
Quotient-recursion _ p (class-extensionalityₗ xy i) = p xy i

module _ where
  open import Structure.Function
  open import Structure.Setoid

  -- Constructs a function on a quotient type from a function on a setoid.
  Quotient-function : ∀{ℓₑ₁ ℓₑ₂}{equiv-A : Equiv{ℓₑ₁}(A)}{equiv-B : Equiv{ℓₑ₂}(B)} ⦃ sub : (Equiv._≡_ equiv-B) ⊆₂ Path ⦄ (f : A → B) ⦃ func : Function ⦃ equiv-A ⦄ ⦃ equiv-B ⦄ f ⦄ → (Quotient(Equiv._≡_ equiv-A) → B)
  Quotient-function {equiv-B = equiv-B} f(x) = Quotient-recursion f (sub₂(Equiv._≡_ equiv-B)(Path) ∘ congruence₁ ⦃ _ ⦄ ⦃ _ ⦄ (f)) x

module _ ⦃ equivalence : Equivalence(_▫_) ⦄ ⦃ prop : ∀{x y} → MereProposition(x ▫ y) ⦄ where
  class-extensionalityᵣ : (class{_▫_ = _▫_} x ≡ class y) → (x ▫ y)
  class-extensionalityᵣ {x = x} {y = y} p = sub₂(_≡_)(_→ᶠ_) ⦃ Path-coercion ⦄ xx-xy (reflexivity(_▫_)) where
    xx-xy : (x ▫ x) ≡ (x ▫ y)
    xx-xy i = Quotient-recursion (x ▫_) (\ab → propositional-extensionalityₗ ([↔]-intro (swap(transitivity(_▫_)) (symmetry(_▫_) ab)) (swap(transitivity(_▫_)) ab))) (p i)

  class-extensionality : (class{_▫_ = _▫_} x ≡ class y) ↔ (x ▫ y)
  class-extensionality = [↔]-intro class-extensionalityₗ class-extensionalityᵣ

module Syntax where
  _/_ : (T : Type{ℓ}) → (T → T → Type{ℓₗ}) → Type
  _ / (_▫_) = Quotient(_▫_)

  [_] : T → (T / (_▫_))
  [_] = class
