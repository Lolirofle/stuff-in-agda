module Structure.Operator.Group {ℓ₁} {ℓ₂} where

open import Functional hiding (id)
import      Lvl
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Relator.Equals{ℓ₁}{ℓ₂}
open import Structure.Operator.Properties{ℓ₁}{ℓ₂}
open import Type{ℓ₂}

record Group {T : Type} (_▫_ : T → T → T) : Stmt where
  field
    id : T
    inv : T → T
  field
    associativity  : Associativity    (_▫_)
    identityₗ       : Identityₗ        (_▫_) id
    identityᵣ       : Identityᵣ        (_▫_) id
    inverseₗ        : InverseFunctionₗ (_▫_) id inv
    inverseᵣ        : InverseFunctionᵣ (_▫_) id inv

  commutationₗ : ∀{x y} → (x ▫ y ≡ y ▫ x) ← ((x ▫ y) ▫ inv(x) ≡ y)
  commutationₗ {x}{y} (comm) =
    ([≡]-symmetry
      ([≡]-transitivity([∧]-intro
        ([≡]-transitivity([∧]-intro
          ([≡]-transitivity([∧]-intro
            ([≡]-with-[(_▫ x)]
              ([≡]-symmetry comm)
            )
            (associativity)
          ))
          ([≡]-with-[((x ▫ y) ▫_)] (inverseₗ))
        ))
        (identityᵣ)
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

  commutationᵣ : ∀{x y} → (x ▫ y ≡ y ▫ x) → ((x ▫ y) ▫ inv(x) ≡ y)
  commutationᵣ {x}{y} (comm) =
    ([≡]-transitivity([∧]-intro
      ([≡]-transitivity([∧]-intro
        ([≡]-transitivity([∧]-intro
          ([≡]-with-[(_▫ inv(x))] comm)
          (associativity)
        ))
        ([≡]-with-[(y ▫_)] (inverseᵣ))
      ))
      (identityᵣ)
    ))
  -- x▫y = y▫x //comm
  -- (x▫y)▫inv(x)
  -- = (y▫x)▫inv(x) //[≡]-with-[(expr ↦ expr ▫ inv(x))] (..)
  -- = y▫(x▫inv(x)) //Group.associativity
  -- = y▫id //[≡]-with-[(expr ↦ y ▫ expr)] Group.inverseᵣ
  -- = y //Group.identityᵣ

  commutation : ∀{x y} → (x ▫ y ≡ y ▫ x) ↔ ((x ▫ y) ▫ inv(x) ≡ y)
  commutation = [↔]-intro (commutationₗ) (commutationᵣ)

record AbelianGroup {T : Type} (_▫_ : T → T → T) : Stmt where
  field
    commutativity  : Commutativity (_▫_)
    group          : Group (_▫_)

  identity = Group.identityₗ(group)
  inverse = Group.inverseₗ(group)

  commutation : ∀{x y} → ((x ▫ y) ▫ Group.inv(group)(x) ≡ y)
  commutation = Group.commutationᵣ(group)(commutativity)
