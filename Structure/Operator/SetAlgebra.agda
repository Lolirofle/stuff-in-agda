module Structure.Operator.SetAlgebra {ℓ₁} {ℓ₂} where

import      Lvl
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Relator.Equals{ℓ₁}{ℓ₂}
open import Structure.Operator.Properties{ℓ₁}{ℓ₂}
open import Type{ℓ₂}

record SetAlgebraSym {S : Type} : Type where
  infixl 1002 ∁_
  infixl 1001 _∩_
  infixl 1000 _∪_

  field
    _∪_  : S → S → S -- Union
    _∩_  : S → S → S -- Intersection
    ∁_  : S → S -- Complement
    ∅  : S -- Empty set
    𝐔  : S -- Universal set

record SetAlgebra {S : Type} {{sym : SetAlgebraSym{S}}} : Stmt where
  open SetAlgebraSym {{...}}

  field
    [∪]-commutativity : Commutativity{S}(_∪_)
    [∩]-commutativity : Commutativity{S}(_∩_)

    [∪]-associativity : Associativity{S}(_∪_)
    [∩]-associativity : Associativity{S}(_∩_)

    [∪][∩]-distributivityₗ : Distributivityₗ{S}(_∪_)(_∩_)
    [∩][∪]-distributivityₗ : Distributivityₗ{S}(_∩_)(_∪_)

    [∪]-identityₗ : Identityₗ{S}(_∪_)(∅)
    [∪]-identityᵣ : Identityᵣ{S}(_∪_)(∅)

    [∪]-with-[∁] : ∀{s : S} → (s ∪ ∁(s) ≡ 𝐔)
    [∩]-with-[∁] : ∀{s : S} → (s ∪ ∁(s) ≡ ∅)

  -- TODO: Theorems from https://en.wikipedia.org/wiki/Algebra_of_sets
  -- [∪][∩]-distributivityᵣ : Distributivityᵣ(_∪_ {S})(_∩_ {S})
  -- [∩][∪]-distributivityᵣ : Distributivityᵣ(_∩_ {S})(_∪_ {S})
  -- [∩]-identityₗ : Identityₗ(_∩_ {S})(𝐔 {S})
  -- [∩]-identityᵣ : Identityᵣ(_∩_ {S})(𝐔 {S})
  -- ∀s. s∪s = s
  -- ∀s. s∩s = s
  -- ∀s. s∩𝐔 = 𝐔
  -- ∀s. s∩∅ = ∅
  -- ∀s₁∀s₂. s₁∪(s₁∩s₂) = s₁
  -- ∀s₁∀s₂. s₁∩(s₁∪s₂) = s₁
