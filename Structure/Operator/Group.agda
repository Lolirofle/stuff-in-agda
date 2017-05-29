module Structure.Operator.Group {ℓ₁} {ℓ₂} where

open import Functional
import      Level as Lvl
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Relator.Equals{ℓ₁}{ℓ₂}
open import Structure.Operator.Properties{ℓ₁}{ℓ₂}
open import Type{ℓ₂}

record Group {T : Type} (_▫_ : T → T → T) (id : T) (inv : T → T) : Stmt where
  field
    associativity  : Associativity  (_▫_)
    identityₗ       : Identityₗ       (_▫_) id
    identityᵣ       : Identityᵣ       (_▫_) id
    inverseₗ        : Inverseₗ        (_▫_) id inv
    inverseᵣ        : Inverseᵣ        (_▫_) id inv

record AbelianGroup {T : Type} (_▫_ : T → T → T) (id : T) (inv : T → T) : Stmt where
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
            ([≡]-with-[(_▫ x)]
              ([≡]-symmetry comm)
            )
            (Group.associativity group)
          ))
          ([≡]-with-[((x ▫ y) ▫_)] (Group.inverseₗ group))
        ))
        (Group.identityᵣ group)
      ))
    )
  -- (x▫y)▫inv(x) = y //comm
  -- y = (x▫y)▫inv(x) //[≡]-symmetry
  -- y▫x
  -- = ((x▫y)▫inv(x))▫x //[≡]-with-[(expr ↦ expr ▫ x)] (..)
  -- = (x▫y)▫(inv(x)▫x) //Group.associativity
  -- = (x▫y)▫id //[≡]-with-[ _ ] Group.inverseₗ
  -- = x▫y //Group.identityᵣ
  -- x▫y = y▫x //[≡]-symmetry

  Group-commutationᵣ : ∀{T _▫_ id inv} → (Group {T} (_▫_) id inv) → ∀{x y} → (x ▫ y ≡ y ▫ x) → ((x ▫ y) ▫ inv(x) ≡ y)
  Group-commutationᵣ {_} {_▫_} {id} {inv} group {x} {y} comm =
    ([≡]-transitivity([∧]-intro
      ([≡]-transitivity([∧]-intro
        ([≡]-transitivity([∧]-intro
          ([≡]-with-[(_▫ inv(x))] comm)
          (Group.associativity group)
        ))
        ([≡]-with-[(y ▫_)] (Group.inverseᵣ group))
      ))
      (Group.identityᵣ group)
    ))
  -- x▫y = y▫x //comm
  -- (x▫y)▫inv(x)
  -- = (y▫x)▫inv(x) //[≡]-with-[(expr ↦ expr ▫ inv(x))] (..)
  -- = y▫(x▫inv(x)) //Group.associativity
  -- = y▫id //[≡]-with-[(expr ↦ y ▫ expr)] Group.inverseᵣ
  -- = y //Group.identityᵣ
