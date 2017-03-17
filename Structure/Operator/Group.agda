module Structure.Operator.Group lvl where

open import Logic(lvl)
open import Relator.Equals(lvl)
open import Structure.Operator.Properties(lvl)

record Group {T : Set} (_▫_ : T → T → T) (id : T) (inv : T → T) : Stmt where
  field
    associativity  : Associativity  (_▫_)
    identityₗ       : Identityₗ       (_▫_) id
    identityᵣ       : Identityᵣ       (_▫_) id
    inverseₗ        : Inverseₗ        (_▫_) id inv
    inverseᵣ        : Inverseᵣ        (_▫_) id inv

record AbelianGroup {T : Set} (_▫_ : T → T → T) (id : T) (inv : T → T) : Stmt where
  field
    commutativity  : Commutativity (_▫_)
    group          : Group (_▫_) id inv

Group-commutation : ∀{T _▫_ id inv} → (Group {T} (_▫_) id inv) → ∀{x y} → (x ▫ y ≡ y ▫ x) ↔ ((x ▫ y) ▫ inv(x) ≡ y)
Group-commutation group = [↔]-intro (Group-commutationₗ group) (Group-commutationᵣ group) where
  Group-commutationₗ : ∀{T _▫_ id inv} → (Group {T} (_▫_) id inv) → ∀{x y} → (x ▫ y ≡ y ▫ x) ← ((x ▫ y) ▫ inv(x) ≡ y)
  Group-commutationₗ {_} {_▫_} {id} {inv} group {x} {y} comm =
    ([≡]-symmetry
      ([≡]-transitivity([∧]-intro
        ([≡]-transitivity([∧]-intro
          ([≡]-transitivity([∧]-intro
            ([≡]-with-[(λ expr → expr ▫ x)]
              ([≡]-symmetry comm)
            )
            (Group.associativity group)
          ))
          ([≡]-with-[(λ expr → (x ▫ y) ▫ expr)] (Group.inverseₗ group))
        ))
        (Group.identityᵣ group)
      ))
    )
  -- (x▫y)▫inv(x) = y //comm
  -- y = (x▫y)▫inv(x) //[≡]-symmetry
  -- y▫x
  -- = ((x▫y)▫inv(x))▫x //[≡]-with-[(λ expr → expr ▫ x)] (..)
  -- = (x▫y)▫(inv(x)▫x) //Group.associativity
  -- = (x▫y)▫id //[≡]-with-[ _ ] Group.inverseₗ
  -- = x▫y //Group.identityᵣ
  -- x▫y = y▫x //[≡]-symmetry

  Group-commutationᵣ : ∀{T _▫_ id inv} → (Group {T} (_▫_) id inv) → ∀{x y} → (x ▫ y ≡ y ▫ x) → ((x ▫ y) ▫ inv(x) ≡ y)
  Group-commutationᵣ {_} {_▫_} {id} {inv} group {x} {y} comm =
    ([≡]-transitivity([∧]-intro
      ([≡]-transitivity([∧]-intro
        ([≡]-transitivity([∧]-intro
          ([≡]-with-[(λ expr → expr ▫ inv(x))] comm)
          (Group.associativity group)
        ))
        ([≡]-with-[(λ expr → y ▫ expr)] (Group.inverseᵣ group))
      ))
      (Group.identityᵣ group)
    ))
  -- x▫y = y▫x //comm
  -- (x▫y)▫inv(x)
  -- = (y▫x)▫inv(x) //[≡]-with-[(λ expr → expr ▫ inv(x))] (..)
  -- = y▫(x▫inv(x)) //Group.associativity
  -- = y▫id //[≡]-with-[(λ expr → y ▫ expr)] Group.inverseᵣ
  -- = y //Group.identityᵣ
