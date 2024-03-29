module Structure.Relator.Ordering where

import      Lvl
open import Functional
open import Functional.Instance
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Logic.Propositional.Theorems
open import Structure.Relator
open import Structure.Relator.Properties
  hiding (antisymmetry ; asymmetry ; transitivity ; reflexivity ; irreflexivity ; trichotomy)
open import Structure.Setoid
open import Type
open import Type.Properties.Empty

private variable ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Lvl.Level

-- A weak order formalizes both "less or equals"-relations and "greater or equals"-relations.
module Weak {T : Type{ℓ₁}} (_≤_ : T → T → Stmt{ℓ₂}) where
  record PartialOrder ⦃ equiv : Equiv{ℓ₃}(T) ⦄ : Stmt{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃} where
    constructor intro
    field
      ⦃ relator ⦄      : BinaryRelator(_≤_)
      ⦃ antisymmetry ⦄ : Antisymmetry(_≤_)(_≡_)
      ⦃ transitivity ⦄ : Transitivity(_≤_)
      ⦃ reflexivity ⦄  : Reflexivity (_≤_)

  -- A weak total order is a weak partial order where all objects are ordered.
  -- Also called: Weak Linear order
  record TotalOrder ⦃ equiv : Equiv{ℓ₃}(T) ⦄ : Stmt{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃} where
    constructor intro
    field
      ⦃ partialOrder ⦄ : PartialOrder
      ⦃ totality ⦄     : ConverseTotal(_≤_)
    open PartialOrder(partialOrder) public

  module Properties where
    -- A left extremum is an object which is one of the left-most in the order of all objects.
    record Extremumₗ (e : T) : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
      constructor intro
      field proof : ∀{x : T} → (e ≤ x)

    -- A left extremum is an object which is one of the right-most in the order of all objects.
    record Extremumᵣ (e : T) : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
      constructor intro
      field proof : ∀{x : T} → (x ≤ e)

    Extremum : T → Stmt{ℓ₁ Lvl.⊔ ℓ₂}
    Extremum(e) = Extremumₗ(e) ∨ Extremumᵣ(e)

    module LE where
      Minimum = Extremumₗ
      Maximum = Extremumᵣ

      module Minimum = Extremumₗ
      module Maximum = Extremumᵣ

  extremeₗ : ⦃ _ : ∃(Properties.Extremumₗ) ⦄ → T
  extremeₗ ⦃ e ⦄ = [∃]-witness e

  extremeᵣ : ⦃ _ : ∃(Properties.Extremumᵣ) ⦄ → T
  extremeᵣ ⦃ e ⦄ = [∃]-witness e

  module LE where
    min = extremeₗ
    max = extremeᵣ

module Strict {T : Type{ℓ₁}} (_<_ : T → T → Stmt{ℓ₂}) where
  record PartialOrder ⦃ equiv : Equiv{ℓ₃}(T) ⦄ : Stmt{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃} where
    constructor intro
    field
      ⦃ relator ⦄      : BinaryRelator(_<_)
      ⦃ transitivity ⦄  : Transitivity  (_<_)
      ⦃ asymmetry ⦄     : Asymmetry     (_<_)
      ⦃ irreflexivity ⦄ : Irreflexivity (_<_)

  -- A strict total order is a strict partial order where all objects are ordered.
  -- Also called: Strict linear order
  record TotalOrder ⦃ equiv : Equiv{ℓ₃}(T) ⦄ : Stmt{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃} where
    constructor intro
    field
      ⦃ partialOrder ⦄ : PartialOrder
      ⦃ trichotomy ⦄   : ConverseTrichotomy(_<_)(_≡_)
    open PartialOrder(partialOrder) public

  module Properties where
    -- An ordering of a type is dense when there is an object inbetween every pair of objects with respect to its order.
    record Dense : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
      field
        between : T → T → T
        left    : ∀{x y : T} → ⦃ _ : (x < y) ⦄ → (x < between(x)(y))
        right   : ∀{x y : T} → ⦃ _ : (x < y) ⦄ → (between(x)(y) < y)

    -- An element is left accessible when there is a left-most object in the order when comparing to the element.
    -- It is defined as: An element is accessible when all objects to the left of the object in the order is accessible.
    -- Because this is an inductive definition, it must have a base case (the terminating case) where the proof is vacuously true (an element which is vacuously accessible). This element can be interpreted as the left-most object.
    -- Example using sets and a weak partial order:
    --   S   = ℤ ∪ {a,b,c}
    --   _≤_ = ℤ._≤_ ∪ {(a,b),(b,c₁),(b,c₂),(a,c₁),(a,c₂) , (a,a),(b,b),(c₁,c₁),(c₂,c₂)}
    --   a is accessible because there are no elements lesser than a (∀(x∊S). ¬(x ≤ a)).
    --   b is accessible because only a is lesser than b, and it is accessible.
    --   c₁ is accessible because all elements lesser than c₁ are a and b, and both of them are accessible.
    --   c₂ is accessible because all elements lesser than c₂ are a and b, and both of them are accessible.
    record Accessibleₗ (a : T) : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
      inductive
      pattern
      constructor intro
      field ⦃ proof ⦄ : ∀{x : T} → ⦃ _ : (x < a) ⦄ → Accessibleₗ(x)

    accessible-induction : ∀{P : T → Type{ℓ₃}} → (∀{x} → (∀{prev} → ⦃ _ : (prev < x) ⦄ → P(prev)) → P(x)) → (∀{x} → ⦃ _ : Accessibleₗ(x) ⦄ → P(x))
    accessible-induction proof ⦃ intro ⦄ = proof(accessible-induction proof)

    accessible-recursion : ∀{U : T → Type{ℓ₃}} → ((x : T) → ((prev : T) → ⦃ _ : (prev < x) ⦄ → U(prev)) → U(x)) → ((x : T) → ⦃ _ : Accessibleₗ(x) ⦄ → U(x))
    accessible-recursion previous x ⦃ intro ⦄ = previous x (\x → accessible-recursion previous x)

    open import Relator.Equals renaming (_≡_ to _≡ₑ_)
    accessible-recursion-intro : ∀{P : T → Type{ℓ₃}}{rec : ∀(x) → _ → P(x)}{φ : ∀{x} → P(x) → Type{ℓ₄}}
                               → (∀(y) ⦃ acc-y : Accessibleₗ(y)⦄
                                 → (∀{x} → ⦃ xy : x < y ⦄ → φ{x}(accessible-recursion rec x ⦃ Accessibleₗ.proof acc-y {x} ⦄))
                                 → (accessible-recursion rec y ≡ₑ rec y (\x → accessible-recursion rec x ⦃ Accessibleₗ.proof acc-y {x} ⦄))
                                 → φ{y}(accessible-recursion rec y)
                               )
                               → (∀{x} → ⦃ acc : Accessibleₗ(x) ⦄ → φ(accessible-recursion{U = P} rec x))
                               -- accessible-recursion rec x ⦃ Accessibleₗ.proof acc-y {x} ⦄
    accessible-recursion-intro{φ = φ} step {x} acc-x@⦃ intro ⦃ prev ⦄ ⦄ = step x ⦃ acc-x ⦄
      (\{y} ⦃ xy ⦄ → accessible-recursion-intro{φ = φ} step {y} ⦃ prev{y} ⦃ xy ⦄ ⦄)
      [≡]-intro

    -- TODO: When proving stuff about a function defined using accessible-recursion? accessible-recursion-all-proof : ∀{U}{x} → ⦃ _ : Accessibleₗ(x) ⦄ → P(accessible-recursion)

    -- An order is well-founded when all objects have a left-most element in the order relative to themselves.
    -- It is well-founded when all objects are left accessible.
    -- Note: Not equivalent to the classical definition of well-foundedness. This does not require a construction of the minimal element. (TODO: I think? At least not computable from the relation? So maybe this should be renamed to something else?)
    -- Note: In the context of rewriting, the a well-founded converse is called terminating.
    -- TODO: Maybe move this to ReductionSystems because it is formalized like this in those cases, but well-foundedness is usually defined using some other formula classically?
    WellFounded : Stmt{ℓ₁ Lvl.⊔ ℓ₂}
    WellFounded = ∀ₗ(Accessibleₗ)
    wellfounded = \{a} ⦃ acc ⦄ {x} ⦃ p ⦄ → inferArg(Accessibleₗ.proof {a = a}) ⦃ acc ⦄ {x} ⦃ p ⦄

    wellfounded-induction : ⦃ WellFounded ⦄ → ∀{P : T → Type{ℓ₃}} → (∀{x} → (∀{prev} → ⦃ _ : (prev < x) ⦄ → P(prev)) → P(x)) → (∀{x} → P(x))
    wellfounded-induction proof = accessible-induction proof

    -- A helper function that helps defining a recursive function which is able to depend on all its preceding values without explicit recursion.
    -- Note: When non-dependent
    --   If the function to be defined is not a dependent function, then the type is:
    --   wellfounded-recursion : ∀{U : Type{ℓ₃}} → ((x : T) → ((prev : T) → ⦃ _ : (prev < x) ⦄ → U) → U) → (T → U)
    wellfounded-recursion : ⦃ WellFounded ⦄ → ∀{P : T → Type{ℓ₃}} → ((x : T) → ((prev : T) → ⦃ _ : (prev < x) ⦄ → P(prev)) → P(x)) → ((x : T) → P(x))
    wellfounded-recursion proof x = accessible-recursion proof x

    wellfounded-recursion-intro : ⦃ wf : WellFounded ⦄ → ∀{P : T → Type{ℓ₃}}{rec : ∀(x) → _ → P(x)}{φ : ∀{x} → P(x) → Type{ℓ₄}}
                                → (∀(y)
                                  → (∀{x} → ⦃ xy : x < y ⦄ → φ{x}(wellfounded-recursion rec x))
                                  → (accessible-recursion rec y ≡ₑ rec y (\x → wellfounded-recursion rec x))
                                  → φ{y}(accessible-recursion rec y)
                                )
                                → (∀{x} → φ(accessible-recursion{U = P} rec x))
    wellfounded-recursion-intro{φ = φ} step = accessible-recursion-intro{φ = φ} (\x → step x)

  -- A well-ordering is a well-founded strict total order
  record WellOrder ⦃ equiv : Equiv{ℓ₃}(T) ⦄ : Stmt{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃} where
    instance constructor intro
    field
      ⦃ totalOrder ⦄  : TotalOrder
      ⦃ wellfounded ⦄ : Properties.WellFounded
    open TotalOrder(totalOrder) public
