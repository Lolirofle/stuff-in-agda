module Structure.Operator.Group.Proofs where

open import Functional hiding (id)
open import Functional.Repeat.Order
import      Lvl
open import Lang.Instance
open import Logic.Propositional
open import Logic.Predicate
open import Sets.Setoid
open import Structure.Function.Domain
open import Structure.Operator.Group
open        Structure.Operator.Group.Morphism
open import Structure.Operator.Monoid
open import Structure.Operator.Properties
open import Structure.Operator.Proofs
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Type

module _ {ℓ₁ ℓ₂} {X : Type{ℓ₁}} ⦃ _ : Equiv(X) ⦄ {_▫X_ : X → X → X} ⦃ structureₗ : Group(_▫X_) ⦄ {Y : Type{ℓ₂}} ⦃ _ : Equiv(Y) ⦄ {_▫Y_ : Y → Y → Y} ⦃ structureᵣ : Group(_▫Y_) ⦄ (f : X → Y) where
  monomorphic-cyclic : ⦃ (_▫X_) ↣ (_▫Y_) ⦄ → Cyclic(_▫X_) → Cyclic(_▫Y_)
  monomorphic-cyclic ⦃ [∃]-intro θ ⦃ θ-proof ⦄ ⦄ ([∃]-intro index ⦃ intro a ⦄) = {!!}

{-
module _ {T : Type{ℓ₂}} {_▫_ : T → T → T} ⦃ group : Group(_▫_) ⦄ where
  open Group  {T} ⦃ [≡]-equiv ⦄ {_▫_} (group)
  open Monoid {T} ⦃ [≡]-equiv ⦄ {_▫_} (monoid)

  commutationₗ : ∀{x y} → (x ▫ y ≡ y ▫ x) ← ((x ▫ y) ▫ inv (x) ≡ y)
  commutationₗ {x}{y} (comm) =
    symmetry(
      ([≡]-with(_▫ x)
        (symmetry comm)
      )
      🝖 (associativity)
      🝖 ([≡]-with((x ▫ y) ▫_)) (inverseₗ)
      🝖 (identityᵣ)
    )
  -- (x▫y)▫inv(x) = y //comm
  -- y = (x▫y)▫inv(x) //[≡]-symmetry
  -- y▫x
  -- = ((x▫y)▫inv(x))▫x //[≡]-with(expr ↦ expr ▫ x) (..)
  -- = (x▫y)▫(inv(x)▫x) //Group.associativity
  -- = (x▫y)▫id //[≡]-with(_) Group.inverseₗ
  -- = x▫y //Group.identityᵣ
  -- x▫y = y▫x //[≡]-symmetry

  commutationᵣ : ∀{x y} → (x ▫ y ≡ y ▫ x) → ((x ▫ y) ▫ inv(x) ≡ y)
  commutationᵣ {x}{y} (comm) =
    ([≡]-with(_▫ inv(x)) comm)
    🝖 (associativity)
    🝖 ([≡]-with(y ▫_) (inverseᵣ))
    🝖 (identityᵣ)
  -- x▫y = y▫x //comm
  -- (x▫y)▫inv(x)
  -- = (y▫x)▫inv(x) //[≡]-with(expr ↦ expr ▫ inv(x)) (..)
  -- = y▫(x▫inv(x)) //Group.associativity
  -- = y▫id //[≡]-with(expr ↦ y ▫ expr) Group.inverseᵣ
  -- = y //Group.identityᵣ

module _ {T : Type} {_▫_ : T → T → T} ⦃ commGroup : CommutativeGroup(_▫_) ⦄ where
  open CommutativeGroup {T} ⦃ [≡]-equiv ⦄ {_▫_} (commGroup)
  open Group            {T} ⦃ [≡]-equiv ⦄ {_▫_} (group)
  open Monoid           {T} ⦃ [≡]-equiv ⦄ {_▫_} (monoid)

  commutation : ∀{x y} → ((x ▫ y) ▫ inv(x) ≡ y)
  commutation = commutationᵣ(commutativity)

module _ {T : Type} {_▫_ : T → T → T} ⦃ associativity : Associativity(_▫_) ⦄ where
  associate4-123-321 : ∀{a b c d} → (((a ▫ b) ▫ c) ▫ d ≡ a ▫ (b ▫ (c ▫ d)))
  associate4-123-321 {a}{b}{c}{d} = associativity 🝖 associativity

  associate4-123-213 : ∀{a b c d} → (((a ▫ b) ▫ c) ▫ d ≡ (a ▫ (b ▫ c)) ▫ d)
  associate4-123-213 {a}{b}{c}{d} = [≡]-with(_▫ d) associativity

  associate4-321-231 : ∀{a b c d} → (a ▫ (b ▫ (c ▫ d)) ≡ a ▫ ((b ▫ c) ▫ d))
  associate4-321-231 {a}{b}{c}{d} = [≡]-with(a ▫_) (symmetry associativity)
-}
