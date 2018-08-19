module Sets.PredicateSet.Proofs where

import      Lvl
open import Functional
import      Logic.Propositional          as Logic
import      Logic.Propositional.Theorems as Logic
import      Logic.Predicate
import      Sets.PredicateSet
import      Structure.Relator.Properties
import      Type

-- [⊆][⊇]-equivalence : ∀{A}{B} → (A ⊆ B) ↔ (B ⊇ A)

module _ {ℓₗ}{ℓₒ} {T : Set(ℓₒ)} where
  open Sets.PredicateSet
  open Structure.Relator.Properties

  private
    Stmt = Logic.Stmt{ℓₗ Lvl.⊔ ℓₒ}

    PredSet' : Set(Lvl.𝐒(ℓₗ Lvl.⊔ ℓₒ))
    PredSet' = PredSet{ℓₗ}{ℓₒ} (T)

    _⊆'_ : PredSet' → PredSet' → Stmt
    _⊆'_ = _⊆_ {ℓₗ}{ℓₗ} {ℓₒ} {T}

    _⊇'_ : PredSet' → PredSet' → Stmt
    _⊇'_ = _⊇_ {ℓₗ}{ℓₗ} {ℓₒ} {T}

    _≡'_ : PredSet' → PredSet' → Stmt
    _≡'_ = _≡_ {ℓₗ}{ℓₗ} {ℓₒ} {T}

    -- TODO: PredSet' has a greater level than Stmt? Not possible with Reflexivity or even Logic.Predicate
    -- Refl : (PredSet' → PredSet' → Stmt) → Stmt
    -- Refl(_▫_) = Reflexivity{_}{_} {PredSet'} (_▫_)

    -- TODO: This is alright...
    -- Refl : (T → T → Stmt) → Stmt
    -- Refl(_▫_) = (∀{x : T} → (x ▫ x))

    -- ...but not this
    -- Refl : (PredSet' → PredSet' → Stmt) → Stmt
    -- Refl(_▫_) = (∀{x : PredSet'} → (x ▫ x))

  [⊆]-reflexivity : ∀{A} → (A ⊆' A)
  [⊆]-reflexivity = id

  [⊆]-transitivity : ∀{A B C} → (A ⊆' B) → (B ⊆' C) → (A ⊆' C)
  [⊆]-transitivity ab bc = bc ∘ ab

  [⊆]-antisymmetry : ∀{A B} → (A ⊇' B) → (A ⊆' B) → (A ≡' B)
  [⊆]-antisymmetry = Logic.[∧]-intro
