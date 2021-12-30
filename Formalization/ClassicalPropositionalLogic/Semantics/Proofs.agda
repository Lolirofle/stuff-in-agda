module Formalization.ClassicalPropositionalLogic.Semantics.Proofs where

import      Lvl
open import Data
open import Data.Boolean
open import Data.Either as Either using (_‖_ ; Left ; Right)
open import Formalization.ClassicalPropositionalLogic.Syntax
open import Formalization.ClassicalPropositionalLogic.Semantics
open import Functional
open import Logic.Classical     as Logic using (Classical)
import      Logic.Propositional as Logic
open import Logic.Propositional.Equiv
import      Logic.Predicate     as Logic
open import Relator.Equals
open import Relator.Equals.Proofs
open import Sets.PredicateSet using (PredSet ; _∈_ ; _∉_ ; _∪_ ; _∪•_ ; _∖_ ; _⊆_ ; _⊇_ ; ∅ ; [≡]-to-[⊆] ; [≡]-to-[⊇]) renaming (•_ to singleton ; _≡_ to _≡ₛ_)
open import Structure.Relator
open import Type

private variable ℓₚ ℓ : Lvl.Level
private variable P : Type{ℓₚ}
private variable 𝔐 : Model(P)
private variable Γ Γ₁ Γ₂ : Formulas(P){ℓ}
private variable φ ψ : Formula(P)

[⊧₊]-antimonotone : (Γ₁ ⊆ Γ₂) → ((_⊧₊ Γ₁) ⊇ (_⊧₊ Γ₂))
[⊧₊]-antimonotone Γ₁Γ₂ 𝔐Γ₂ Γ₁γ = 𝔐Γ₂ (Γ₁Γ₂ Γ₁γ)

[⊧₊]-strengthen : (𝔐 ⊧₊ Γ₁) → (𝔐 ⊧₊ Γ₂) → (𝔐 ⊧₊ (Γ₁ ∪ Γ₂))
[⊧₊]-strengthen 𝔐Γ₁ 𝔐Γ₂ Γ₁Γ₂γ = Logic.[∨]-elim 𝔐Γ₁ 𝔐Γ₂ Γ₁Γ₂γ

[⊧₊]-of-[∪]ₗ : (𝔐 ⊧₊ (Γ₁ ∪ Γ₂)) → (𝔐 ⊧₊ Γ₁)
[⊧₊]-of-[∪]ₗ 𝔐Γ₁Γ₂ 𝔐Γ₁ = 𝔐Γ₁Γ₂ (Left 𝔐Γ₁)

[⊧₊]-of-[∪]ᵣ : (𝔐 ⊧₊ (Γ₁ ∪ Γ₂)) → (𝔐 ⊧₊ Γ₂)
[⊧₊]-of-[∪]ᵣ 𝔐Γ₁Γ₂ 𝔐Γ₂ = 𝔐Γ₁Γ₂ (Right 𝔐Γ₂)

[⊧]-to-[⊧₊] : (𝔐 ⊧ φ) Logic.↔ (𝔐 ⊧₊ singleton(φ))
[⊧]-to-[⊧₊] = Logic.[↔]-intro (_$ [≡]-intro) (\𝔐φ φγ → substitute₂-₂ᵣ(_⊧_)(_) φγ 𝔐φ)

[⊧]-contradiction : (𝔐 ⊧ φ) → (𝔐 ⊧ (¬ φ)) → (𝔐 ⊧ ⊥)
[⊧]-contradiction = apply

[⊨]-monotone : (Γ₁ ⊆ Γ₂) → ((Γ₁ ⊨_) ⊆ (Γ₂ ⊨_))
[⊨]-monotone Γ₁Γ₂ Γ₁φ 𝔐Γ₂ = Γ₁φ (Γ₁γ ↦ 𝔐Γ₂ (Γ₁Γ₂ Γ₁γ))

[⊨]-functionₗ : (Γ₁ ≡ₛ Γ₂) → ((Γ₁ ⊨_) ≡ₛ (Γ₂ ⊨_))
[⊨]-functionₗ {Γ₁ = Γ₁}{Γ₂ = Γ₂} Γ₁Γ₂ {φ} = Logic.[↔]-intro ([⊨]-monotone{Γ₁ = Γ₂}{Γ₂ = Γ₁}(\{x} → [≡]-to-[⊇] (Γ₁Γ₂{x}) {x}){φ}) ([⊨]-monotone{Γ₁ = Γ₁}{Γ₂ = Γ₂}(\{x} → [≡]-to-[⊆] (Γ₁Γ₂{x}) {x}){φ})

[⊨]-weaken : (Γ₁ ⊨ φ) → ((Γ₁ ∪ Γ₂) ⊨ φ)
[⊨]-weaken Γ₁φ 𝔐Γ₁Γ₂ = Γ₁φ (Γ₁γ ↦ 𝔐Γ₁Γ₂ (Left Γ₁γ))

[⊨]-validity : (∀{Γ : Formulas(P){ℓ}} → (Γ ⊨ φ)) Logic.↔ Valid(φ)
[⊨]-validity = Logic.[↔]-intro (λ r → const r) (λ l → l{∅} empty)

[⊨]-contradiction : (Γ ⊨ φ) → (Γ ⊨ (¬ φ)) → (Γ ⊨ ⊥)
[⊨]-contradiction Γφ Γ¬φ 𝔐Γ = Γ¬φ 𝔐Γ (Γφ 𝔐Γ)

[⊨]-unsatisfiability : (Γ ⊨ ⊥) Logic.↔ Unsatisfiable(Γ)
[⊨]-unsatisfiability {Γ = Γ} = Logic.[↔]-intro l r where
  l : (Γ ⊨ ⊥) ← Unsatisfiable(Γ)
  l unsatΓ {𝔐} 𝔐Γ = unsatΓ (Logic.[∃]-intro 𝔐 ⦃ 𝔐Γ ⦄)

  r : (Γ ⊨ ⊥) → Unsatisfiable(Γ)
  r Γ⊥ (Logic.[∃]-intro 𝔐 ⦃ 𝔐Γ ⦄) = Γ⊥ 𝔐Γ

[⊨][¬]-intro : ((Γ ∪ singleton(φ)) ⊨ ⊥) Logic.↔ (Γ ⊨ (¬ φ))
[⊨][¬]-intro {Γ = Γ}{φ = φ} = Logic.[↔]-intro l r where
  l : ((Γ ∪ singleton(φ)) ⊨ ⊥) ← (Γ ⊨ (¬ φ))
  l Γ¬φ 𝔐Γφ = Γ¬φ (𝔐Γφ ∘ Left) (𝔐Γφ (Right [≡]-intro))

  r : ((Γ ∪ singleton(φ)) ⊨ ⊥) → (Γ ⊨ (¬ φ))
  r Γφ⊥ 𝔐Γ 𝔐φ = Γφ⊥ ([⊧₊]-strengthen {Γ₁ = Γ}{Γ₂ = singleton(φ)} 𝔐Γ (Logic.[↔]-to-[→] [⊧]-to-[⊧₊] 𝔐φ))

[∅]-satisfiable : Satisfiable{P = P}{ℓ = ℓ}(∅)
[∅]-satisfiable = Logic.[∃]-intro (const(𝑇)) ⦃ \{_}() ⦄

module _ ⦃ classical : ∀{ℓ} → Logic.∀ₗ(Classical{ℓ}) ⦄ where
  [⊧]-of-[¬¬] : (𝔐 ⊧ ¬(¬ φ)) → (𝔐 ⊧ φ)
  [⊧]-of-[¬¬] {𝔐 = 𝔐}{φ = φ} = Logic.[¬¬]-elim

  [⊨]-entailment-unsatisfiability : (Γ ⊨ φ) Logic.↔ Unsatisfiable(Γ ∪ singleton(¬ φ))
  [⊨]-entailment-unsatisfiability {Γ = Γ}{φ = φ} = Logic.[↔]-intro l r where
    l : (Γ ⊨ φ) ← Unsatisfiable(Γ ∪ singleton(¬ φ))
    l r {𝔐} 𝔐Γ = [⊧]-of-[¬¬] {𝔐 = 𝔐}{φ = φ} (𝔐¬φ ↦ r (Logic.[∃]-intro 𝔐 ⦃ Logic.[∨]-elim 𝔐Γ (\{[≡]-intro → 𝔐¬φ}) ⦄))

    r : (Γ ⊨ φ) → Unsatisfiable(Γ ∪ singleton(¬ φ))
    r l (Logic.[∃]-intro 𝔐 ⦃ sat ⦄) = [⊧]-contradiction {φ = φ} 𝔐φ 𝔐¬φ where
      𝔐φ  = l([⊧₊]-of-[∪]ₗ {Γ₁ = Γ} sat)
      𝔐¬φ = Logic.[↔]-to-[←] [⊧]-to-[⊧₊] ([⊧₊]-of-[∪]ᵣ {Γ₁ = Γ} sat)

  [⊨][⟶]-intro : ((Γ ∪ singleton(φ)) ⊨ ψ) Logic.↔ (Γ ⊨ (φ ⟶ ψ))
  [⊨][⟶]-intro {Γ = Γ}{φ = φ}{ψ = ψ} = Logic.[↔]-intro l r where
    l : (Γ ⊨ (φ ⟶ ψ)) → ((Γ ∪ singleton(φ)) ⊨ ψ)
    l φψ {𝔐 = 𝔐} 𝔐Γφ = Logic.[∨]-elim (¬φ ↦ Logic.[⊥]-elim(¬φ 𝔐φ)) id (φψ 𝔐Γ) where
      𝔐Γ : 𝔐 ⊧₊ Γ
      𝔐Γ {γ} Γγ = 𝔐Γφ {γ} (Logic.[∨]-introₗ Γγ)

      𝔐φ : 𝔐 ⊧ φ
      𝔐φ = 𝔐Γφ {φ} (Logic.[∨]-introᵣ [≡]-intro)

    r : ((Γ ∪ singleton(φ)) ⊨ ψ) → (Γ ⊨ (φ ⟶ ψ))
    r Γφψ {𝔐 = 𝔐} 𝔐Γ with Logic.excluded-middle(𝔐 ⊧ φ)
    ... | Logic.[∨]-introₗ 𝔐φ  = Logic.[∨]-introᵣ (Γφψ(Logic.[∨]-elim 𝔐Γ \{[≡]-intro → 𝔐φ}))
    ... | Logic.[∨]-introᵣ ¬𝔐φ = Logic.[∨]-introₗ ¬𝔐φ
