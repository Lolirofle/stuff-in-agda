module Structure.Relator.Apartness.Proofs where

open import Data
open import Data.Either as Either
open import Data.Tuple as Tuple
open import Functional
open import Logic.Classical
open import Logic.Propositional
open import Logic.Propositional.Theorems
import      Lvl
open import Structure.Relator.Apartness
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Syntax.Implication
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓ₃ ℓₗ ℓₗ₁ ℓₗ₂ ℓₗ₃ ℓₗ₄ ℓₑ ℓₑ₁ ℓₑ₂ ℓₑ₃ ℓₑ₄ : Lvl.Level
private variable T A B : Type{ℓ}
private variable _▫_ : T → T → Type{ℓ}

module _ {_▫_ : T → T → Type{ℓ}} where
  instance
    -- The negation of an apartness relation is an equivalence relation.
    -- This is a reason for using an apartness relation in constructive real mathematics. Both the apartness properties and the equivalence properties are sought after and by starting with an apartness relation, one gets both.
    apartness-equivalenceᵣ : ⦃ apart : Apartness(_▫_) ⦄ → Equivalence((¬_) ∘₂ (_▫_))
    Reflexivity.proof  (Equivalence.reflexivity  apartness-equivalenceᵣ) = irreflexivity(_▫_)
    Symmetry.proof     (Equivalence.symmetry     apartness-equivalenceᵣ) = contrapositiveᵣ(symmetry(_▫_))
    Transitivity.proof (Equivalence.transitivity apartness-equivalenceᵣ) nxy nyz = [∨]-elim nxy nyz ∘ cotransitivity(_▫_)

  module _ ⦃ classical : Classical₂(_▫_) ⦄ where
    equivalence-apartnessᵣ : ⦃ equi : Equivalence(_▫_) ⦄ → Apartness((¬_) ∘₂ (_▫_))
    Irreflexivity.proof  (Apartness.irreflexivity  equivalence-apartnessᵣ) = [¬¬]-intro (reflexivity(_▫_))
    Symmetry.proof       (Apartness.symmetry       equivalence-apartnessᵣ) = contrapositiveᵣ(symmetry(_▫_))
    CoTransitivity.proof (Apartness.cotransitivity equivalence-apartnessᵣ) {x}{y}{z} nxz with excluded-middle(x ▫ y) | excluded-middle(y ▫ z)
    ... | Left  xy  | Left  yz  with () ← nxz(transitivity(_▫_) xy yz)
    ... | Left  xy  | Right nyz = [∨]-introᵣ nyz
    ... | Right nxy | Left  yz  = [∨]-introₗ nxy
    ... | Right nxy | Right nyz = [∨]-introₗ nxy

    equivalence-apartnessₗ : ⦃ apart : Apartness((¬_) ∘₂ (_▫_)) ⦄ → Equivalence(_▫_)
    Reflexivity.proof  (Equivalence.reflexivity equivalence-apartnessₗ) = [¬¬]-elim(irreflexivity((¬_) ∘₂ (_▫_)))
    Symmetry.proof     (Equivalence.symmetry equivalence-apartnessₗ) = contrapositiveₗ(symmetry((¬_) ∘₂ (_▫_)))
    Transitivity.proof (Equivalence.transitivity equivalence-apartnessₗ) {x}{y}{z} xy yz with excluded-middle(x ▫ z)
    ... | Left xz   = xz
    ... | Right nxz with cotransitivity((¬_) ∘₂ (_▫_)) nxz
    ... |   Left  nxy with () ← nxy xy
    ... |   Right nyz with () ← nyz yz

    apartness-equivalenceₗ : ⦃ equi : Equivalence((¬_) ∘₂ (_▫_)) ⦄ → Apartness(_▫_)
    Irreflexivity.proof (Apartness.irreflexivity apartness-equivalenceₗ) = reflexivity((¬_) ∘₂ (_▫_))
    Symmetry.proof (Apartness.symmetry apartness-equivalenceₗ) = contrapositiveₗ(symmetry((¬_) ∘₂ (_▫_)))
    CoTransitivity.proof (Apartness.cotransitivity apartness-equivalenceₗ) {x}{y}{z} =
      (x ▫ z)                ⇒-[ [¬¬]-intro ]
      ¬¬(x ▫ z)              ⇒-[ contrapositiveᵣ(uncurry(transitivity((¬_) ∘₂ (_▫_)))) ]
      ¬(¬(x ▫ y) ∧ ¬(y ▫ z)) ⇒-[ [¬]-preserves-[∧][∨]ᵣ ]
      ¬¬(x ▫ y) ∨ ¬¬(y ▫ z)  ⇒-[ Either.map [¬¬]-elim [¬¬]-elim ]
      (x ▫ y) ∨ (y ▫ z)      ⇒-end
