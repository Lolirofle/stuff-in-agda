module Structure.Operator.Field where

import      Lvl
open import Logic
open import Logic.Propositional
open import Sets.Setoid
open import Structure.Operator.Group using (Group ; CommutativeGroup)
open import Structure.Operator.Monoid using (Monoid)
open import Structure.Operator.Properties hiding (distributivityₗ ; distributivityᵣ)
open import Type
-- open import Sets.PredicateSet.Filter

record Field {ℓ} {T : Type{ℓ}} ⦃ _ : Equiv(T) ⦄ (_+_  : T → T → T) (_⋅_  : T → T → T) : Stmt{ℓ} where
  -- TODO
  -- _⋅ₙ_ : Filter() → Filter() → Filter()
  -- _⋅ₙ_ = 

  field
    instance ⦃ [+]-commutative-group ⦄ : CommutativeGroup (_+_)
    instance ⦃ [⋅]-monoid ⦄            : Monoid (_⋅_)
    -- instance ⦃ [⋅]-inverse-existence ⦄ : ∃(InverseFunction (_⋅ₙ_))
    instance ⦃ distributivityₗ ⦄       : Distributivityₗ (_⋅_) (_+_)
    instance ⦃ distributivityᵣ ⦄       : Distributivityᵣ (_⋅_) (_+_)

  -- [⋅]-inv : (x : T) → ⦃ _ : (x ≢ id) ⦄ → T
  -- [⋅]-inv = ... ([∃]-witness [⋅]-inverse-existence)

  instance
    [+]-group : Group(_+_)
    [+]-group = CommutativeGroup.group([+]-commutative-group)

  instance
    [+]-monoid : Monoid(_+_)
    [+]-monoid = Group.monoid([+]-group)
