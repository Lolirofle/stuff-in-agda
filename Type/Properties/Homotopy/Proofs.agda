module Type.Properties.Homotopy.Proofs where

import      Data.Tuple as Tuple
open import Logic
open import Logic.Classical
open import Logic.Predicate
open import Logic.Propositional
import      Lvl
open import Type
open import Type.Properties.Homotopy
open import Type.Properties.MereProposition
open import Type.Properties.Singleton
open import Structure.Function.Domain
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Structure.Setoid.WithLvl
open import Structure.Type.Identity
open import Syntax.Function
open import Syntax.Transitivity

private variable ℓ ℓₑ ℓₑₑ ℓₚ : Lvl.Level
private variable T : Type{ℓ}

module _ ⦃ equiv : ∀{ℓ}{T : Type{ℓ}} → Equiv{ℓ}(T) ⦄ where
  private open module EquivEquiv{ℓ}{T} = Equiv(equiv{ℓ}{T}) using () renaming (_≡_ to _≡ₑ_)

  module _ ⦃ identElim : ∀{ℓ}{T : Type{ℓ}} → IdentityEliminator(_≡ₑ_ {T = T}) ⦄ where
    constant-endofunction-existence-on-equivalence-is-hset : ∀{x y : T} → ∃{Obj = (x ≡ y) → (x ≡ y)}(Constant) → HomotopyLevel(2)(T)
    constant-endofunction-existence-on-equivalence-is-hset ([∃]-intro const) {x = x} {y} {xy₁} {xy₂} = {!!} where
      equivalence-endofunction-invertibleₗ : ∀{f : ∀{x y : T} → (x ≡ y) → (x ≡ y)} → (∀{x y : T} → Invertibleₗ(f{x}{y}))
      ∃.witness (equivalence-endofunction-invertibleₗ {T = T}{f = f} {x}{y}) xy =
        xy 🝖 symmetry(_≡ₑ_) (f(reflexivity _))
      Tuple.left (∃.proof equivalence-endofunction-invertibleₗ) = {!!}
      Inverseₗ.proof (Tuple.right (∃.proof (equivalence-endofunction-invertibleₗ {T = T}{f = f} {x}{y}))) {xy} = idElim(_≡ₑ_) ⦃ inst = identElim{T = T} ⦄ (xy ↦ (f(xy) 🝖 symmetry(_≡ₑ_) (f(reflexivity(_≡ₑ_))) ≡ₑ xy)) {!!} xy

{-
module _ ⦃ equiv : Equiv{ℓₑ}(T) ⦄ ⦃ equiv-equiv : Equiv{ℓₑ}(Equiv._≡_ equiv) ⦄ where
    -- TODO: ComputablyDecidable → UIP (https://homotopytypetheory.org/2012/03/30/a-direct-proof-of-hedbergs-theorem/)
    -- TODO: http://www.cse.chalmers.se/~nad/listings/equality/Equality.Decidable-UIP.html
  classical-to-uip : (∀{x y : T} → ((x ≡ y) ∨ (x ≢ y))) → UniqueIdentityProofs(T)
  MereProposition.uniqueness (classical-to-uip {T = T} dec {x} {y}) {xy₁} {xy₂} = {!p xy₁!} where
    {-
    p : ∀{x y : T} → (x ≡ y) → Stmt
    p {x}{y} eq with dec{x}{x} | dec{x}{y}
    ... | [∨]-introₗ xx  | [∨]-introₗ xy  = eq ≡ transitivity(_≡_) xx xy
    ... | [∨]-introₗ xx  | [∨]-introᵣ nxy with () ← nxy eq
    ... | [∨]-introᵣ nxx | [∨]-introₗ _   with () ← nxx [≡]-intro
    -}

    dec-eq : ∀{x y} → (x ≡ y) → (x ≡ y)
    dec-eq {x}{y} eq with dec{x}{y}
    ... | [∨]-introₗ xy  = xy
    ... | [∨]-introᵣ nxy with () ← nxy eq

    dec-eq-unique : ∀{x y}{xy₁ xy₂ : x ≡ y} → (dec-eq xy₁ ≡ dec-eq xy₂)
    dec-eq-unique {x}{y} {xy₁} with dec{x}{y}
    ... | [∨]-introₗ _   = ?
    ... | [∨]-introᵣ nxy with () ← nxy xy₁

    dec-eq-unit : ∀{x y}{eq : x ≡ y} → (eq ≡ dec-eq eq)
    dec-eq-unit  {x}{y}{eq} with dec{y}{y} | dec{x}{y}
    ... | [∨]-introₗ yy | [∨]-introₗ xy = {!!}
    ... | [∨]-introₗ yy | [∨]-introᵣ x₂ = {!!}
    ... | [∨]-introᵣ x₁ | [∨]-introₗ x₂ = {!!}
    ... | [∨]-introᵣ x₁ | [∨]-introᵣ x₂ = {!!}

{-    p : ∀{x y : T} → (xy : x ≡ y) → (xy ≡ dec-eq(xy))
    p {x}{y} [≡]-intro with dec{x}{x} | dec{x}{y}
    ... | [∨]-introₗ a | [∨]-introₗ x₁ = {![≡]-intro!}
    ... | [∨]-introₗ a | [∨]-introᵣ x₁ = {!!}
    ... | [∨]-introᵣ a | [∨]-introₗ x₁ = {!!}
    ... | [∨]-introᵣ a | [∨]-introᵣ x₁ = {!!}
-}
-}
