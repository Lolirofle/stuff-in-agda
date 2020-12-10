import      Lvl
open import Type

module Structure.Logic.Constructive.BoundedPredicate
  {ℓₗ}  {Formula : Type{ℓₗ}}
  {ℓₘₗ} (Proof : Formula → Type{ℓₘₗ})
  {ℓₚ}  {Predicate : Type{ℓₚ}}
  {ℓₒ}  {Domain : Type{ℓₒ}}
  (_$_ : Predicate → (x : Domain) → ∀{B : Domain → Formula} → Proof(B(x)) → Formula)
  where

import      Logic.Predicate as Meta
open import Type.Dependent using (Σ)
open import Type.Properties.Inhabited using (◊)
import      Structure.Logic.Constructive.Propositional as Propositional
open import Syntax.Function

private variable P : Predicate
private variable X Y Q : Formula
private variable x y z : Domain
private variable B : Domain → Formula

-- Rules of universal quantification (for all).
record BoundedUniversal(∀ₗ : (Domain → Formula) → Predicate → Formula) : Type{ℓₘₗ Lvl.⊔ Lvl.of(Formula) Lvl.⊔ Lvl.of(Domain) Lvl.⊔ Lvl.of(Predicate)} where
  field
    intro : (∀{x} → (bx : Proof(B(x))) → Proof((P $ x) {B} bx)) → Proof(∀ₗ B P)
    elim  : Proof(∀ₗ B P) → ∀{x} → (bx : Proof(B(x))) → Proof((P $ x) {B} bx)
∀ₗ = \ ⦃(Meta.[∃]-intro ▫) : Meta.∃(BoundedUniversal)⦄ → ▫
module ∀ₛ {▫} ⦃ p ⦄ = BoundedUniversal {▫} p

-- Rules of existential quantification (exists).
record BoundedExistential(∃ : (Domain → Formula) → Predicate → Formula) : Type{ℓₘₗ Lvl.⊔ Lvl.of(Formula) Lvl.⊔ Lvl.of(Domain) Lvl.⊔ Lvl.of(Predicate)} where
  field
    intro : (bx : Proof(B(x))) → Proof((P $ x) {B} bx) → Proof(∃ B P)
    elim  : (∀{x} → (bx : Proof(B(x))) → Proof((P $ x) {B} bx) → Proof(Q)) → (Proof(∃ B P) → Proof(Q))
∃ = \ ⦃(Meta.[∃]-intro ▫) : Meta.∃(BoundedExistential)⦄ → ▫
module ∃ₛ {▫} ⦃ p ⦄ = BoundedExistential {▫} p

record BoundedExistentialWitness(∃ : (Domain → Formula) → Predicate → Formula) : Type{ℓₘₗ Lvl.⊔ Lvl.of(Formula) Lvl.⊔ Lvl.of(Domain) Lvl.⊔ Lvl.of(Predicate)} where
  field
    witness : Proof(∃ B P) → Domain
    bound   : (p : Proof(∃ B P)) → Proof(B(witness p))
    proof   : (p : Proof(∃ B P)) → Proof((P $ witness p) {B} (bound p))

record Logic : Type{ℓₘₗ Lvl.⊔ Lvl.of(Formula) Lvl.⊔ Lvl.of(Domain) Lvl.⊔ Lvl.of(Predicate)} where
  field
    ⦃ propositional ⦄ : Propositional.Logic(Proof)
    ⦃ universal ⦄     : Meta.∃(BoundedUniversal)
    ⦃ existential ⦄   : Meta.∃(BoundedExistential)
