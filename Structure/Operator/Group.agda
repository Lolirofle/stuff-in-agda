module Structure.Operator.Group lvl where

open import Logic(lvl)
open import Relator.Equals(lvl)
open import Structure.Operator.Properties(lvl)

record Group {T : Stmt} (_▫_ : T → T → T) (id : T) (inv : T → T) : Stmt where
  field
    associativity  : Associativity  (_▫_)
    identityₗ       : Identityₗ       (_▫_) id
    identityᵣ       : Identityᵣ       (_▫_) id
    inverseₗ        : Inverseₗ        (_▫_) id inv
    inverseᵣ        : Inverseᵣ        (_▫_) id inv

record AbelianGroup {T : Stmt} (_▫_ : T → T → T) (id : T) (inv : T → T) : Stmt where
  field
    commutativity  : Commutativity  (_▫_)
    associativity  : Associativity  (_▫_)
    identityₗ       : Identityₗ       (_▫_) id
    identityᵣ       : Identityᵣ       (_▫_) id
    inverseₗ        : Inverseₗ        (_▫_) id inv
    inverseᵣ        : Inverseᵣ        (_▫_) id inv

-- Group-inverseᵣ : ∀ {T _▫_ id inv} → (Group {T} (_▫_) id inv) → (Inverseᵣ {T} (_▫_) id inv)
-- Group-inverseᵣ group =
--   [≡]-transitivity([∧]-intro
--     (Group.commutativity group)
--     (Group.inverse group)
--   )

-- Group-identityᵣ : ∀ {T _▫_ id inv} → (Group {T} (_▫_) id inv) → (Identityᵣ {T} (_▫_) id)
-- Group-identityᵣ group =
--   [≡]-transitivity([∧]-intro
--     (Group.commutativity group)
--     (Group.identity group)
--   )

Group-commutation : ∀ {T _▫_ id inv} → (Group {T} (_▫_) id inv) → ∀ {x y} → (x ▫ y ≡ y ▫ x) → ((x ▫ y) ▫ inv(x) ≡ y)
Group-commutation {_} {_▫_} {id} {inv} group {x} {y} comm =
  ([≡]-transitivity([∧]-intro
    ([≡]-transitivity([∧]-intro
      ([≡]-transitivity([∧]-intro
        ([≡]-with-[(λ expr → expr ▫ inv(x))] comm)
        (Group.associativity group)
      ))
      ([≡]-with-[(λ expr → y ▫ expr)] (Group.inverseₗ group))
    ))
    (Group.identityᵣ group)
  ))
-- x▫y = y▫x
-- (x▫y)▫inv(x)
-- = (y▫x)▫inv(x)
-- = y▫(x▫inv(x))
-- = y▫id
-- = y
-- (x▫y)▫inv(x) = y
