module Structure.Operator.Group {ℓ₁} {ℓ₂} where

open import Functional hiding (id)
import      Lvl
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Relator.Equals{ℓ₁}{ℓ₂}
open import Relator.Equals.Theorems{ℓ₁}{ℓ₂}
open import Structure.Operator.Monoid{ℓ₁}{ℓ₂}
open import Structure.Operator.Properties{ℓ₁}{ℓ₂}
open import Structure.Relator.Properties{ℓ₁}{ℓ₂}
open import Type{ℓ₂}

-- A type and a binary operator using this type is a group when:
-- • It is a monoid.
-- • The operator have an inverse in both directions.
record Group {T : Type} (_▫_ : T → T → T) : Stmt where
  open Monoid ⦃ ... ⦄ 

  field
    inv : T → T
  field
    ⦃ monoid ⦄ : Monoid{T} (_▫_)
    inverseₗ     : InverseFunctionₗ (_▫_) (id ⦃ monoid ⦄) inv
    inverseᵣ     : InverseFunctionᵣ (_▫_) (id ⦃ monoid ⦄) inv

  commutationₗ : ∀{x y} → (x ▫ y ≡ y ▫ x) ← ((x ▫ y) ▫ inv(x) ≡ y)
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

-- Multiplicative Group
record MultGroup {T : Type} (_▫_ : T → T → T) (𝟎 : T) : Stmt where
  open Monoid ⦃ ... ⦄ 

  field
    inv : (x : T) → ⦃ _ : x ≢ 𝟎 ⦄ → T
  field
    ⦃ monoid ⦄ : Monoid{T} (_▫_)
    inverseₗ        : ∀{x} → ⦃ nonzero : (x ≢ 𝟎) ⦄ → ((inv x ⦃ nonzero ⦄) ▫ x) ≡ id ⦃ monoid ⦄
    inverseᵣ        : ∀{x} → ⦃ nonzero : (x ≢ 𝟎) ⦄ → (x ▫ (inv x ⦃ nonzero ⦄)) ≡ id ⦃ monoid ⦄

  identity = identityₗ
  inverse = inverseₗ

record AbelianGroup {T : Type} (_▫_ : T → T → T) : Stmt where
  open Group ⦃ ... ⦄ 
  open Monoid ⦃ ... ⦄ 

  field
    commutativity  : Commutativity (_▫_)
    ⦃ group ⦄    : Group (_▫_)

  identity = identityₗ
  inverse = inverseₗ

  commutation : ∀{x y} → ((x ▫ y) ▫ (inv ⦃ group ⦄)(x) ≡ y)
  commutation = commutationᵣ(commutativity)
