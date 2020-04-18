import      Lvl
open import Structure.Category
open import Structure.Setoid
open import Type

module Structure.Category.Morphism.IdTransport
  {ℓₒ ℓₘ : Lvl.Level}
  {Obj : Type{ℓₒ}}
  {Morphism : Obj → Obj → Type{ℓₘ}}
  ⦃ morphism-equiv : ∀{x y : Obj} → Equiv(Morphism x y) ⦄
  (cat : Category(Morphism) ⦃ morphism-equiv ⦄)
  where

import      Functional.Dependent as Fn
import      Function.Equals
open        Function.Equals.Dependent
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Relator.Equals using ([≡]-intro) renaming (_≡_ to _≡ₑ_)
open import Relator.Equals.Proofs
import      Structure.Category.Names as Names
open import Structure.Category.Properties
open import Structure.Function
open import Structure.Relator.Properties

open Names.ArrowNotation(Morphism)
open Category(cat)
open Morphism.OperModule ⦃ morphism-equiv ⦄ (\{x} → _∘_ {x})
open Morphism.IdModule   ⦃ morphism-equiv ⦄ (\{x} → _∘_ {x})(id)

private variable a b c : Obj

transport : (a ≡ₑ b) → (a ⟶ b)
transport = sub₂(_≡ₑ_)(_⟶_) ⦃ [≡]-sub-of-reflexive ⦃ intro id ⦄ ⦄

transport-function : Function ⦃ [≡]-equiv ⦄ ⦃ morphism-equiv ⦄ (transport {a = a}{b = b})
Function.congruence transport-function xy = sub₂(_≡ₑ_)(_≡_) ⦃ [≡]-sub-of-reflexive ⦃ Equiv.reflexivity(morphism-equiv) ⦄ ⦄ ([≡]-with(transport) xy)

transport-of-reflexivity : (transport(reflexivity(_≡ₑ_)) ≡ id{a})
transport-of-reflexivity = reflexivity(_≡_) ⦃ Equiv.reflexivity morphism-equiv ⦄

-- transport-of-symmetry : ∀{ab : (a ≡ₑ b)}{ba : (b ≡ₑ a)} → (transitivity(_≡ₑ_) ab ba ≡ reflexivity(_≡ₑ_)) → (transport(symmetry(_≡ₑ_) ab) ≡ transport ba)

transport-of-transitivity : ∀{ab : (a ≡ₑ b)}{bc : (b ≡ₑ c)} → (transport(transitivity(_≡ₑ_) ab bc) ≡ transport(bc) ∘ transport(ab))
transport-of-transitivity {ab = [≡]-intro} {bc = [≡]-intro} = symmetry(_≡_) ⦃ Equiv.symmetry morphism-equiv ⦄ (Morphism.identityₗ(_∘_)(id))

[∘]-on-transport-inverseₗ : ∀{ab : (a ≡ₑ b)} → ((transport (symmetry(_≡ₑ_) ab)) ∘ (transport ab) ≡ id)
[∘]-on-transport-inverseₗ {ab = [≡]-intro} = Morphism.identityₗ(_∘_)(id)

instance
  transport-inverseₗ : ∀{ab : (a ≡ₑ b)} → Inverseₗ(transport ab) (transport(symmetry(_≡ₑ_) ab))
  transport-inverseₗ {ab = ab} = Morphism.intro ([∘]-on-transport-inverseₗ {ab = ab})

[∘]-on-transport-inverseᵣ : ∀{ab : (a ≡ₑ b)} → ((transport ab) ∘ (transport (symmetry(_≡ₑ_) ab)) ≡ id)
[∘]-on-transport-inverseᵣ {ab = [≡]-intro} = Morphism.identityᵣ(_∘_)(id)

instance
  transport-inverseᵣ : ∀{ab : (a ≡ₑ b)} → Inverseᵣ(transport ab) (transport(symmetry(_≡ₑ_) ab))
  transport-inverseᵣ {ab = ab} = Morphism.intro ([∘]-on-transport-inverseᵣ {ab = ab})

instance
  transport-isomorphism : ∀{ab : (a ≡ₑ b)} → Isomorphism(transport ab)
  transport-isomorphism {ab = ab} = [∃]-intro (transport(symmetry(_≡_) ab)) ⦃ [∧]-intro (transport-inverseₗ {ab = ab}) (transport-inverseᵣ {ab = ab}) ⦄

transport-congruence-symmetry-involution : ∀{ab : (a ≡ₑ b)} → ((transport Fn.∘ symmetry(_≡ₑ_) Fn.∘ symmetry(_≡ₑ_)) ab ≡ transport ab)
transport-congruence-symmetry-involution {ab = [≡]-intro} = reflexivity(_≡_) ⦃ Equiv.reflexivity morphism-equiv ⦄
