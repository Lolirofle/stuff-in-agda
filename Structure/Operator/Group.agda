module Structure.Operator.Group where

open import Logic
open import Relator.Equals
open import Structure.Operator.Properties

record Group {T : Set} (_▫_ : T → T → T) (id : T) (inv : T → T) : Set where
  field
    commutativity  : Commutativity  (_▫_)
    associativity  : Associativity  (_▫_)
    identity       : Identityₗ       (_▫_) id
    inverse        : Inverseₗ        (_▫_) id inv

Group-inverseᵣ : {T : Set} → {_▫_ : T → T → T} → {id : T} → {inv : T → T} → (Group {T} (_▫_) id inv) → (Inverseᵣ {T} (_▫_) id inv)
Group-inverseᵣ group = [≡]-transitivity([∧]-intro (Group.commutativity group) (Group.inverse group))

Group-identityᵣ : {T : Set} → {_▫_ : T → T → T} → {id : T} → {inv : T → T} → (Group {T} (_▫_) id inv) → (Identityᵣ {T} (_▫_) id)
Group-identityᵣ group =
  [≡]-transitivity([∧]-intro (Group.commutativity group) (Group.identity group))
