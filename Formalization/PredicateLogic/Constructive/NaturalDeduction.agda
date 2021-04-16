open import Formalization.PredicateLogic.Signature

module Formalization.PredicateLogic.Constructive.NaturalDeduction (𝔏 : Signature) where
open Signature(𝔏)

open import Data.ListSized
import      Lvl
open import Formalization.PredicateLogic.Syntax(𝔏)
open import Formalization.PredicateLogic.Syntax.Substitution(𝔏)
open import Functional using (_∘_ ; _∘₂_ ; swap)
open import Numeral.Finite
open import Numeral.Natural
open import Relator.Equals.Proofs.Equiv
open import Sets.PredicateSet using (PredSet ; _∈_ ; _∉_ ; _∪_ ; _∪•_ ; _∖_ ; _⊆_ ; _⊇_ ; ∅ ; [≡]-to-[⊆] ; [≡]-to-[⊇]) renaming (•_ to · ; _≡_ to _≡ₛ_)
open import Type

private variable ℓ : Lvl.Level
private variable args vars : ℕ
private variable Γ : PredSet{ℓ}(Formula(vars))

data _⊢_ {ℓ} : PredSet{ℓ}(Formula(vars)) → Formula(vars) → Type{Lvl.𝐒(ℓₚ Lvl.⊔ ℓₒ Lvl.⊔ ℓ)} where
  direct : (Γ ⊆ (Γ ⊢_))

  [⊤]-intro : (Γ ⊢ ⊤)

  [⊥]-elim  : ∀{φ} → (Γ ⊢ ⊥) → (Γ ⊢ φ)

  [∧]-intro : ∀{φ ψ} → (Γ ⊢ φ) → (Γ ⊢ ψ) → (Γ ⊢ (φ ∧ ψ))
  [∧]-elimₗ : ∀{φ ψ} → (Γ ⊢ (φ ∧ ψ)) → (Γ ⊢ φ)
  [∧]-elimᵣ : ∀{φ ψ} → (Γ ⊢ (φ ∧ ψ)) → (Γ ⊢ ψ)

  [∨]-introₗ : ∀{φ ψ} → (Γ ⊢ φ) → (Γ ⊢ (φ ∨ ψ))
  [∨]-introᵣ : ∀{φ ψ} → (Γ ⊢ ψ) → (Γ ⊢ (φ ∨ ψ))
  [∨]-elim   : ∀{φ ψ χ} → ((Γ ∪ · φ) ⊢ χ) → ((Γ ∪ · ψ) ⊢ χ) → (Γ ⊢ (φ ∨ ψ)) → (Γ ⊢ χ)

  [⟶]-intro : ∀{φ ψ} → ((Γ ∪ · φ) ⊢ ψ) → (Γ ⊢ (φ ⟶ ψ))
  [⟶]-elim  : ∀{φ ψ} → (Γ ⊢ φ) → (Γ ⊢ (φ ⟶ ψ)) → (Γ ⊢ ψ)

  [Ɐ]-intro : ∀{φ} → (∀{t} → (Γ ⊢ (substitute0 t φ))) → (Γ ⊢ (Ɐ φ))
  [Ɐ]-elim  : ∀{φ} → (Γ ⊢ (Ɐ φ)) → ∀{t} → (Γ ⊢ (substitute0 t φ))

  [∃]-intro : ∀{φ}{t} → (Γ ⊢ (substitute0 t φ)) → (Γ ⊢ (∃ φ))
  [∃]-elim  : ∀{φ ψ} → (∀{t} → (Γ ∪ ·(substitute0 t φ)) ⊢ ψ) → (Γ ⊢ (∃ φ)) → (Γ ⊢ ψ)
