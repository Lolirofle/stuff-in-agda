module Structure.Operator.Group lvl where

open import Logic(lvl)
open import Relator.Equals(lvl)
open import Structure.Operator.Properties(lvl)

record Group {T : Stmt} (_▫_ : T → T → T) (id : T) (inv : T → T) : Stmt where
  field
    commutativity  : Commutativity  (_▫_)
    associativity  : Associativity  (_▫_)
    identity       : Identityₗ       (_▫_) id
    inverse        : Inverseₗ        (_▫_) id inv

Group-inverseᵣ : {T : Stmt} → {_▫_ : T → T → T} → {id : T} → {inv : T → T} → (Group {T} (_▫_) id inv) → (Inverseᵣ {T} (_▫_) id inv)
Group-inverseᵣ group = [≡]-transitivity([∧]-intro (Group.commutativity group) (Group.inverse group))

Group-identityᵣ : {T : Stmt} → {_▫_ : T → T → T} → {id : T} → {inv : T → T} → (Group {T} (_▫_) id inv) → (Identityᵣ {T} (_▫_) id)
Group-identityᵣ group =
  [≡]-transitivity([∧]-intro (Group.commutativity group) (Group.identity group))
