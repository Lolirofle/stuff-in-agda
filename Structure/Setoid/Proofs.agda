module Structure.Setoid.Proofs where

import Lvl
open import Functional
open import Logic
open import Logic.Propositional
open import Structure.Setoid.WithLvl
open import Structure.Function
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties

{-


module _ where
  private variable ℓ ℓ₁ ℓ₂ ℓ₃ : Level
  private variable A B : Type{ℓ}
  private variable P : Stmt{ℓ}

  Choice : (A → B → Stmt{ℓ}) → Stmt
  Choice{A = A}{B = B}(_▫_) = (∀{x} → ∃(y ↦ x ▫ y)) → (∃{Obj = A → B}(f ↦ ∀{x} → (x ▫ f(x))))

  module _ ⦃ choice : ∀{ℓ₁ ℓ₂ ℓ₃}{A : Type{ℓ₁}}{B : Type{ℓ₂}}{_▫_ : A → B → Stmt{ℓ₃}} → Choice(_▫_) ⦄ where
    open import Data.Boolean
    open import Structure.Relator.Properties
    open import Structure.Relator.Properties.Proofs
    open import Relator.Equals.Proofs.Equiv

    thing : Stmt{ℓ} → Bool → Bool → Stmt
    thing P a b = (a ≡ b) ∨ P

    thing-functionallyTotal : ∀{x} → ∃(y ↦ thing P x y)
    thing-functionallyTotal {x = x} = [∃]-intro x ⦃ [∨]-introₗ (reflexivity(_≡_)) ⦄

    thing-choice : ∃(f ↦ ∀{x} → thing(P) x (f(x)))
    thing-choice {P = P} = choice{_▫_ = thing P} thing-functionallyTotal

    instance
      thing-reflexivity : Reflexivity(thing(P))
      Reflexivity.proof thing-reflexivity = [∨]-introₗ(reflexivity(_≡_))

    instance
      thing-symmetry : Symmetry(thing(P))
      Symmetry.proof thing-symmetry = [∨]-elim2 (symmetry(_≡_)) id

    instance
      thing-transitivity : Transitivity(thing(P))
      Transitivity.proof thing-transitivity ([∨]-introₗ xy) ([∨]-introₗ yz) = [∨]-introₗ (transitivity(_) xy yz)
      Transitivity.proof thing-transitivity ([∨]-introₗ xy) ([∨]-introᵣ p)  = [∨]-introᵣ p
      Transitivity.proof thing-transitivity ([∨]-introᵣ p)  _               = [∨]-introᵣ p

    thing-ext : let ([∃]-intro f) = thing-choice{P = P} in ∀{a b} → thing(P) a b → (f(a) ≡ f(b))
    thing-ext ([∨]-introₗ ab) = congruence₁([∃]-witness thing-choice) ab
    thing-ext {a = a} {b = b} ([∨]-introᵣ p) = {!!}

    thing-eq : let ([∃]-intro f) = thing-choice{P = P} in (P ↔ (f(𝐹) ≡ f(𝑇)))
    _⨯_.left  (thing-eq {P = P}) ft with [∃]-proof (thing-choice{P = P}){𝐹}
    _⨯_.left (thing-eq {P = P}) ft | [∨]-introₗ ff = [∨]-syllogismₗ ([∃]-proof (thing-choice{P = P}){𝑇}) ((symmetry(_≢_) ⦃ negated-symmetry ⦄ ∘ [↔]-to-[←] [≢][𝑇]-is-[𝐹] ∘ symmetry(_≡_)) (transitivity(_≡_) ff ft))
    _⨯_.left (thing-eq {P = P}) ft | [∨]-introᵣ p = p
    _⨯_.right (thing-eq {P = P}) p = thing-ext ([∨]-introᵣ p)

    bool-eq-classical : Classical₂ {X = Bool} (_≡_)

    choice-to-classical : Classical(P)
    excluded-middle ⦃ choice-to-classical {P = P} ⦄ with excluded-middle ⦃ bool-eq-classical {[∃]-witness (thing-choice{P = P}) 𝐹} {[∃]-witness (thing-choice{P = P}) 𝑇} ⦄
    excluded-middle ⦃ choice-to-classical {P = P} ⦄ | [∨]-introₗ ft  = [∨]-introₗ ([↔]-to-[←] thing-eq ft)
    excluded-middle ⦃ choice-to-classical {P = P} ⦄ | [∨]-introᵣ nft = [∨]-introᵣ (nft ∘ [↔]-to-[→] thing-eq)

  module _ ⦃ classical : ∀{ℓ}{P : Stmt{ℓ}} → Classical(P) ⦄ where
    proof-irrelevance : ∀{p₁ p₂ : P} → (p₁ ≡ p₂)
    proof-irrelevance with excluded-middle
    proof-irrelevance {P = P}{p₁}{p₂} | [∨]-introₗ p  = {!!}
    proof-irrelevance {P = P}{p₁}{p₂} | [∨]-introᵣ np = [⊥]-elim(np p₁)


-}
