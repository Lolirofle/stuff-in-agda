import      Lvl
open import Type

module Structure.Logic.Constructive.Predicate
  {ℓₗ}  {Formula : Type{ℓₗ}}
  {ℓₘₗ} (Proof : Formula → Type{ℓₘₗ})
  {ℓₚ}  {Predicate : Type{ℓₚ}}
  {ℓₒ}  {Domain : Type{ℓₒ}}
  (_$_ : Predicate → Domain → Formula)
  where

import      Logic.Predicate as Meta
import      Structure.Logic.Constructive.Propositional as Propositional
open import Type.Properties.Inhabited using (◊)

private variable P : Predicate
private variable X Y Q : Formula
private variable x y z : Domain

-- Rules of universal quantification (for all).
record Universal(∀ₗ : Predicate → Formula) : Type{ℓₘₗ Lvl.⊔ Lvl.of(Formula) Lvl.⊔ Lvl.of(Domain) Lvl.⊔ Lvl.of(Predicate)} where
  field
    intro : (∀{x} → Proof(P $ x)) → Proof(∀ₗ P)
    elim  : Proof(∀ₗ P) → ∀{x} → Proof(P $ x)
∀ₗ = \ ⦃(Meta.[∃]-intro ▫) : Meta.∃(Universal)⦄ → ▫
module ∀ₗ {▫} ⦃ p ⦄ = Universal {▫} p

-- Rules of existential quantification (exists).
record Existential(∃ : Predicate → Formula) : Type{ℓₘₗ Lvl.⊔ Lvl.of(Formula) Lvl.⊔ Lvl.of(Domain) Lvl.⊔ Lvl.of(Predicate)} where
  field
    intro : Proof(P $ x) → Proof(∃ P)
    elim  : (∀{x} → Proof(P $ x) → Proof(Q)) → (Proof(∃ P) → Proof(Q))
∃ = \ ⦃(Meta.[∃]-intro ▫) : Meta.∃(Existential)⦄ → ▫
module ∃ {▫} ⦃ p ⦄ = Existential {▫} p

record ExistentialWitness(∃ : Predicate → Formula) : Type{ℓₘₗ Lvl.⊔ Lvl.of(Formula) Lvl.⊔ Lvl.of(Domain) Lvl.⊔ Lvl.of(Predicate)} where
  field
    witness : Proof(∃ P) → Domain
    proof   : (p : Proof(∃ P)) → Proof(P $ witness p)

NonEmptyDomain = ◊ Domain

record Equality(_≡_ : Domain → Domain → Formula) : Type{ℓₘₗ Lvl.⊔ Lvl.of(Formula) Lvl.⊔ Lvl.of(Domain) Lvl.⊔ Lvl.of(Domain)} where
  field
    reflexivity : Proof(x ≡ x)
    substitute  : (P : Domain → Formula) → Proof(x ≡ y) → (Proof(P(x)) → Proof(P(y)))

record Logic : Type{ℓₘₗ Lvl.⊔ Lvl.of(Formula) Lvl.⊔ Lvl.of(Domain) Lvl.⊔ Lvl.of(Predicate)} where
  field
    ⦃ propositional ⦄ : Propositional.Logic(Proof)
    ⦃ universal ⦄     : Meta.∃(Universal)
    ⦃ existential ⦄   : Meta.∃(Existential)
